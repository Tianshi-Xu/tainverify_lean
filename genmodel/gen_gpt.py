#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

"""

GPT-2 small style, single GPU:

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 \
/data/home/xts/miniconda3/envs/verdict/bin/torchrun \
    --nproc_per_node=1 \
    genmodel/gen_gpt.py --policy dp \
        --layers 12 \
        --hidden 768 \
        --heads 12 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 1 \
        --gbs 1 \
        --mbs 1 \
        --seqlen 1024 \
        --vocab_size 50257

GPT-2 small style, tensor parallel size 4:

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 \
/data/home/xts/miniconda3/envs/verdict/bin/torchrun \
    --nproc_per_node=1 \
    genmodel/gen_gpt.py --policy tp \
        --layers 12 \
        --hidden 768 \
        --heads 12 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 4 \
        --gbs 1 \
        --mbs 1 \
        --seqlen 1024 \
        --vocab_size 50257
"""
import sys
sys.setrecursionlimit(10000)

import os
import shutil
import torch

import nnscaler
from nnscaler.parallel import parallelize, ComputeConfig

from model.gpt import GPT, Config, dummy_data

import argparse
parser = argparse.ArgumentParser(description='MLP example')
parser.add_argument('--policy', type=str,
                    help='policy choice, starting with "PAS"')
parser.add_argument('--dim', type=int, default=1024, help='model hidden size')
parser.add_argument('--gbs', type=int, default=4, help='global batch size')
parser.add_argument('--mbs', type=int, default=4, help='micro batch size')
parser.add_argument('--fp16', action='store_true',
                    default=False, help='use fp16 for the training')
parser.add_argument('--dp_size', type=int, default=1,
                    help='size of data parallelism')
parser.add_argument('--pp_size', type=int, default=1,
                    help='size of pipeline parallelism')
parser.add_argument('--tp_size', type=int, default=1,
                    help='size of tensor parallelism')
parser.add_argument('--zero', action='store_true',
                    default=False, help='use zero1 for the training')

parser.add_argument('--layers', type=int, default=4,
                    help='number of transformer layers')
parser.add_argument('--hidden', type=int, default=1024, help='hidden size')
parser.add_argument('--heads', type=int, default=16,
                    help='number of attention heads')
parser.add_argument('--seqlen', type=int, default=2048, help='sequence length')
parser.add_argument('--vocab_size', type=int, default=51200, help='vocabulary size')
args = parser.parse_args()


nnscaler.init()
if args.gbs % args.mbs != 0:
    raise ValueError(
        'global batch size should be divisible by micro batch size')


# model
config = Config(
    hidden=args.hidden,
    layers=args.layers,
    heads=args.heads,
    ffn_hidden_dim=4*args.hidden,
    num_embeddings=args.vocab_size,
    seqlen=args.seqlen,
)
model = GPT(config)
model = model if not args.fp16 else model.half()

# dummy_input
input_ids, position_ids = dummy_data(args.mbs, config)
dummy_input = {"input_ids": input_ids, "position_ids": position_ids}

# get policy
policy_name = 'pas_' + args.policy
policy = args.policy  # use the builtin policies

# compute_config
compute_config = ComputeConfig(
    plan_ngpus=args.pp_size * args.tp_size,
    runtime_ngpus=args.dp_size * args.tp_size * args.pp_size,
    use_zero=args.zero,
    use_end2end=True,
    constant_folding=True,
    use_pipeline=args.pp_size > 1,
    pipeline_nmicros=args.gbs // args.dp_size // args.mbs,
    pipeline_nstages=args.pp_size,
    pas_config={
        # customized settings that can affect code generation.
        '_pas_name': args.policy,
        '_gbs': args.gbs,
        '_pp_size': args.pp_size,
        '_tp_size': args.tp_size,
        '_dp_size': args.dp_size,
        # for autodist only
        'update_freq': args.gbs // args.mbs,
        'use_fp16': args.fp16,
    },
    user_config={
        'mbs': args.mbs,
        'fp16': args.fp16,
    }
)


# parallelization
pmodel = parallelize(
    module_or_module_class=model,
    dummy_input=dummy_input,
    pas_policy=policy,
    compute_config=compute_config,
    gen_savedir='./.nnscaler',
    reuse="override",
    load_module=False,
    # instance_name: Optional[str] = None,
    # load_module: bool = True,
    # module_dtype:  Optional[torch.dtype] = None,
    # module_fn: Optional[Callable[[], torch.nn.Module]] = None,
    # init_module_params: bool = True,
    # broadcast_strategy: Union[str, BroadcastGenFilesStrategy] = 'none',
)


dp = args.dp_size
pp = args.pp_size
tp = args.tp_size
gbs = args.gbs
mbs = args.mbs
dim = args.hidden
layers = args.layers
hidden = args.hidden
heads = args.heads
seqlen = args.seqlen
vocab_size = args.vocab_size
nm = gbs//dp//mbs if args.policy in ["hybrid", "pp"] else 1
fname = f"gpt_mgener_dp{args.dp_size}_pp{args.pp_size}_tp{args.tp_size}_nm{nm}_gbs{gbs}_dim{dim}_ly{layers}_h{heads}_hi{hidden}_sq{seqlen}_voc{vocab_size}"

file = "mgener.pkl"
dst = f"genmodel/mgeners/{fname}.pkl"
try:
    shutil.move(file, dst)
    print("MGENER:", dst)
except:
    pass
