#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

import torch
from torch import nn
import math


class Attention(nn.Module):
    """
    A simple multi-head attention block without positional encoding (ROPE).
    Uses basic nn.Linear layers for Q, K, V projections.
    """
    def __init__(self, dim: int, num_heads: int = 8, nlayers: int = 1):
        super().__init__()
        assert dim % num_heads == 0, "dim must be divisible by num_heads"
        
        self.dim = dim
        self.num_heads = num_heads
        self.head_dim = dim // num_heads
        self.scale = math.sqrt(self.head_dim)
        
        self.layers = nn.ModuleList([])
        for _ in range(nlayers):
            self.layers.append(nn.ModuleDict({
                'q_proj': nn.Linear(dim, dim, bias=False),
                'k_proj': nn.Linear(dim, dim, bias=False),
                'v_proj': nn.Linear(dim, dim, bias=False),
                'o_proj': nn.Linear(dim, dim, bias=False),
            }))

    def forward(self, x):
        """
        Args:
            x: input tensor of shape (batch_size, seq_len, dim)
        Returns:
            loss: scalar loss (sum of output)
        """
        batch_size, seq_len, _ = x.shape
        
        for layer in self.layers:
            # Q, K, V projections
            q = layer['q_proj'](x)  # (batch_size, seq_len, dim)
            k = layer['k_proj'](x)
            v = layer['v_proj'](x)
            
            # Reshape for multi-head attention
            # (batch_size, seq_len, num_heads, head_dim) -> (batch_size, num_heads, seq_len, head_dim)
            q = q.view(batch_size, seq_len, self.num_heads, self.head_dim).transpose(1, 2)
            k = k.view(batch_size, seq_len, self.num_heads, self.head_dim).transpose(1, 2)
            v = v.view(batch_size, seq_len, self.num_heads, self.head_dim).transpose(1, 2)
            
            # Attention scores: (batch_size, num_heads, seq_len, seq_len)
            attn_weights = torch.matmul(q, k.transpose(-2, -1)) / self.scale
            attn_weights = torch.softmax(attn_weights, dim=-1)
            
            # Attention output: (batch_size, num_heads, seq_len, head_dim)
            attn_output = torch.matmul(attn_weights, v)
            
            # Reshape back: (batch_size, seq_len, dim)
            attn_output = attn_output.transpose(1, 2).contiguous().view(batch_size, seq_len, self.dim)
            
            # Output projection
            x = layer['o_proj'](attn_output)
        
        loss = torch.sum(x)
        return loss
