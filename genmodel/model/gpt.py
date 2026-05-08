#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

import torch
import torch.nn.functional as F
from dataclasses import dataclass
from torch import nn
import math


@dataclass
class Config:
    hidden: int = 1024
    layers: int = 8
    heads: int = 16
    ffn_hidden_dim: int = 4096
    num_embeddings: int = 51200
    seqlen: int = 1024
    dropout: float = 0.2
    attn_dropout: float = 0.2
    activation_dropout: float = 0.2


def build_gpt_config(name: str) -> Config:
    if name == 'toy':
        hidden, layers, heads = 1024, 4, 16
    elif name == '350M':
        hidden, layers, heads = 1024, 24, 16
    elif name == '760M':
        hidden, layers, heads = 1536, 24, 16
    elif name == '1.3B':
        hidden, layers, heads = 2048, 24, 32
    elif name == '2.6B':
        hidden, layers, heads = 2560, 32, 32
    elif name == '6.7B':
        hidden, layers, heads = 4096, 32, 32
    elif name == '15B':
        hidden, layers, heads = 5120, 48, 40
    elif name == '39B':
        hidden, layers, heads = 8192, 48, 64
    elif name == '175B':
        hidden, layers, heads = 12288, 96, 96
    else:
        assert False, f'unrecognized name: {name}'
    return Config(
        hidden=hidden,
        layers=layers,
        heads=heads,
        ffn_hidden_dim=4 * hidden,
    )


class SelfAttention(torch.nn.Module):
    def __init__(self, cfg: Config):
        super().__init__()
        assert cfg.hidden % cfg.heads == 0, "hidden must be divisible by heads"
        self.hidden = cfg.hidden
        self.heads = cfg.heads
        self.head_dim = cfg.hidden // cfg.heads
        self.scale = math.sqrt(self.head_dim)

        self.q_proj = nn.Linear(cfg.hidden, cfg.hidden, bias=False)
        self.k_proj = nn.Linear(cfg.hidden, cfg.hidden, bias=False)
        self.v_proj = nn.Linear(cfg.hidden, cfg.hidden, bias=False)
        self.o_proj = nn.Linear(cfg.hidden, cfg.hidden, bias=False)

    def forward(self, x: torch.Tensor):
        batch_size, seq_len, _ = x.shape

        q = self.q_proj(x)
        k = self.k_proj(x)
        v = self.v_proj(x)

        q = q.view(batch_size, seq_len, self.heads, self.head_dim).transpose(1, 2)
        k = k.view(batch_size, seq_len, self.heads, self.head_dim).transpose(1, 2)
        v = v.view(batch_size, seq_len, self.heads, self.head_dim).transpose(1, 2)

        attn_scores = torch.matmul(q, k.transpose(-2, -1)) / self.scale
        attn_weights = torch.softmax(attn_scores, dim=-1)
        attn_output = torch.matmul(attn_weights, v)
        attn_output = (
            attn_output.transpose(1, 2)
            .contiguous()
            .view(batch_size, seq_len, self.hidden)
        )
        return self.o_proj(attn_output)


class FeedForward(torch.nn.Module):
    def __init__(self, cfg: Config):
        super().__init__()
        self.fc1 = nn.Linear(cfg.hidden, cfg.ffn_hidden_dim, bias=False)
        self.fc2 = nn.Linear(cfg.ffn_hidden_dim, cfg.hidden, bias=False)

    def forward(self, x: torch.Tensor):
        return self.fc2(F.gelu(self.fc1(x)))


class GPTBlock(torch.nn.Module):
    def __init__(self, cfg: Config):
        super().__init__()
        self.attn_norm = nn.LayerNorm(cfg.hidden)
        self.attn = SelfAttention(cfg)
        self.ffn_norm = nn.LayerNorm(cfg.hidden)
        self.ffn = FeedForward(cfg)

    def forward(self, x: torch.Tensor):
        x = x + self.attn(self.attn_norm(x))
        x = x + self.ffn(self.ffn_norm(x))
        return x


class GPT(torch.nn.Module):

    def __init__(self, cfg: Config):
        super().__init__()

        # self.embed = torch.nn.Embedding(cfg.num_embeddings, cfg.hidden)
        self.embedw = torch.nn.Parameter(torch.empty(cfg.num_embeddings, cfg.hidden))
        torch.nn.init.normal_(self.embedw, mean=0.0, std=0.02)
        self.position = torch.nn.Embedding(cfg.seqlen, cfg.hidden)
        # Keep the exported graph deterministic for Lean denotation/proofs.
        self.embed_dropout = torch.nn.Identity()
        self.lm_head = nn.Linear(cfg.hidden, cfg.num_embeddings, bias=False)

        self.layers = torch.nn.ModuleList(
            [GPTBlock(cfg) for _ in range(cfg.layers)]
        )
        self.final_layernorm = torch.nn.LayerNorm(cfg.hidden)

    def forward(self, input_ids: torch.Tensor, position_ids: torch.Tensor):

        # embed = self.embed(input_ids)
        embed = torch.nn.functional.embedding(
            input_ids, self.embedw, padding_idx=None,
            max_norm=None, norm_type=2., scale_grad_by_freq=False, sparse=False
        )
        pos_embed = self.position(position_ids)
        embed = embed + pos_embed
        embed = self.embed_dropout(embed)
        enc = embed

        for layer in self.layers:
            enc = layer(enc)
        enc = self.final_layernorm(enc)

        logits = self.lm_head(enc)
        # simplified
        loss = torch.sum(logits)
        return loss


def dummy_data(batch_size: int, cfg: Config):

    input_ids = torch.randint(
        0, cfg.num_embeddings,
        size=(batch_size, cfg.seqlen,),
        dtype=torch.int64,
        device=torch.cuda.current_device()
    )
    position_ids = torch.arange(
        0, cfg.seqlen, dtype=torch.int64,
        device=torch.cuda.current_device()
    ).repeat(batch_size, 1).view(batch_size, cfg.seqlen,)

    return input_ids, position_ids
