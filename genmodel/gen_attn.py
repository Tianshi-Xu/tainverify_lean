#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

"""
PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=1  \
    genmodel/gen_attn.py --policy dp \
        --dim 128 \
        --num_heads 8 \
        --layers 1 \
        --seq_len 64 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 1 \
        --gbs 16 \
        --mbs 16 

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=1  \
    genmodel/gen_attn.py --policy hybrid \
        --dim 1024 \
        --num_heads 16 \
        --layers 1 \
        --seq_len 128 \
        --dp_size 2 \
        --pp_size 2 \
        --tp_size 2 \
        --gbs 1024 \
        --mbs 256

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=1  \
    genmodel/gen_attn.py --policy tp \
        --dim 128 \
        --num_heads 8 \
        --layers 2 \
        --seq_len 64 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 4 \
        --gbs 16 \
        --mbs 16

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=2  \
    genmodel/gen_attn.py --policy tp \
        --dim 128 \
        --num_heads 8 \
        --layers 2 \
        --seq_len 64 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 2 \
        --gbs 16 \
        --mbs 16

PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=4  \
    genmodel/gen_attn.py --policy hybrid \
        --dim 256 \
        --num_heads 8 \
        --layers 2 \
        --seq_len 64 \
        --dp_size 1 \
        --pp_size 2 \
        --tp_size 2 \
        --gbs 16 \
        --mbs 16
"""

import torch

import nnscaler
from nnscaler.parallel import parallelize, ComputeConfig

from model.attn import Attention


import argparse
parser = argparse.ArgumentParser(description='Attention example')
parser.add_argument('--policy', type=str, help='policy choice, starting with "PAS"')
parser.add_argument('--dim', type=int, default=1024, help='model hidden size')
parser.add_argument('--num_heads', type=int, default=8, help='number of attention heads')
parser.add_argument('--layers', type=int, default=1, help='number of attention layers')
parser.add_argument('--seq_len', type=int, default=128, help='sequence length')
parser.add_argument('--gbs', type=int, default=4, help='global batch size')
parser.add_argument('--mbs', type=int, default=4, help='micro batch size')
parser.add_argument('--fp16', action='store_true', default=False, help='use fp16 for the training')
parser.add_argument('--dp_size', type=int, default=1, help='size of data parallelism')
parser.add_argument('--pp_size', type=int, default=1, help='size of pipeline parallelism')
parser.add_argument('--tp_size', type=int, default=1, help='size of tensor parallelism')
parser.add_argument('--zero', action='store_true', default=False, help='use zero1 for the training')
args = parser.parse_args()


nnscaler.init()
if args.gbs % args.mbs != 0:
    raise ValueError('global batch size should be divisible by micro batch size')


# model
model = Attention(dim=args.dim, num_heads=args.num_heads, nlayers=args.layers)

# dummy_input
def dummy_data():
    return torch.randn(
        args.mbs, args.seq_len, args.dim, device=torch.cuda.current_device())
dummy_input = {"x": dummy_data()}

# get policy
policy_name = 'pas_' + args.policy

policy = args.policy # use the builtin policies

# compute_config
compute_config=ComputeConfig(
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
    },
    user_config={
        'mbs': args.mbs,
        'seq_len': args.seq_len,
        'num_heads': args.num_heads,
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
)


import shutil, os

dp = args.dp_size
pp = args.pp_size
tp = args.tp_size
gbs = args.gbs
mbs = args.mbs
dim = args.dim
layers = args.layers
seq_len = args.seq_len
num_heads = args.num_heads
nm = gbs//dp//mbs if args.policy in ["hybrid", "pp"] else 1
fname = f"attn_mgener_dp{dp}_pp{pp}_tp{tp}_nm{nm}_gbs{gbs}_dim{dim}_seq{seq_len}_nh{num_heads}_ly{layers}"

file = "mgener.pkl"
dst = f"genmodel/mgeners/{fname}.pkl"
try:
    shutil.move(file, dst)
    print("MGENER:", dst)
except:
    pass
