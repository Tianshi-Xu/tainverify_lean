#!/usr/bin/env python3
"""
Extract L12 zigzag tid mapping from Goal_3.lean

This script helps map each tid referenced in mk_attention(k=3)
to its corresponding tid in L12 zigzag band by analyzing the
graph structure.
"""

import re
import sys

# Load Goal_3.lean
with open('trainverify/denote/yoco_goals/Goal_3.lean') as f:
    goal3 = f.read()

# Split into lines for line-based analysis
lines = goal3.split('\n')

print("=" * 80)
print("L12 ZIGZAG TID EXTRACTION")
print("=" * 80)

# We know L12 SM attention is at line 539 (1-indexed)
# Let's extract context around it
l12_sm_start = 500
l12_sm_end = 570

print(f"\n=== SM SIDE (lines {l12_sm_start}-{l12_sm_end}) ===\n")

sm_nodes = []
for i in range(l12_sm_start-1, l12_sm_end):
    line = lines[i]
    if '{ rank := 0, op :=' in line:
        # Extract tid from outs field
        outs_match = re.search(r'outs := \[(\d+)\]', line)
        op_match = re.search(r'op := "(.*?)"', line)
        ins_match = re.search(r'ins := \[(.*?)\]', line)
        
        if outs_match and op_match:
            out_tid = int(outs_match.group(1))
            op_name = op_match.group(1)
            ins_tids = ins_match.group(1) if ins_match else ""
            
            # Only show tids in the 53xx range (likely L12-related)
            if 5290 <= out_tid <= 5400:
                sm_nodes.append((i+1, out_tid, op_name, ins_tids))
                print(f"Line {i+1:4d}: out={out_tid}, op={op_name}")
                if ins_tids:
                    print(f"             ins=[{ins_tids}]")

# Now let's trace the specific chain leading to attention
print(f"\n=== SM L12 ATTENTION CHAIN ===\n")
print(f"Target: FW_attn_zigzag with output 5347")
print(f"Looking backwards from 5347...")

# Key tids we care about:
# - 5330: carry input (FW_add output, feeds into RMS norm chain)
# - 5332: RMS norm for input 
# - 5334, 5336: projections
# - 5340: RMS norm for queries  
# - 5342: q projection (input to attention)
# - 5343, 5344: k, v (from FW_to ops)
# - 5345, 5346: cu_seqlens (init goals)
# - 5347: attention output

# PM side
l12_pm_start = 1960
l12_pm_end = 2080

print(f"\n=== PM SIDE (lines {l12_pm_start}-{l12_pm_end}) ===\n")

pm_nodes = []
for i in range(l12_pm_start-1, l12_pm_end):
    line = lines[i]
    if '{ rank :=' in line and 'FW_attn_zigzag' in line:
        outs_match = re.search(r'outs := \[(\d+)\]', line)
        ins_match = re.search(r'ins := \[(.*?)\]', line)
        rank_match = re.search(r'rank := (\d+)', line)
        
        if outs_match:
            out_tid = int(outs_match.group(1))
            rank = int(rank_match.group(1)) if rank_match else 0
            ins_tids = ins_match.group(1) if ins_match else ""
            
            print(f"Line {i+1:4d}: rank={rank}, out={out_tid}")
            print(f"             ins=[{ins_tids}]")

# Now, let's create a mapping based on operation type
# For sliding window k=3, mk_attention uses these tids:
# n4844: carry (FW_add output before layer)
# n4846: RMS norm output  
# n4852: v input (fw_per_head_mix_precision_linear output)
# n4854: q input (fw_rotary_embedding output)
# n4855: k input (fw_rotary_embedding output)
# n4856, n4857: cu_seqlens
# n4858: attention output

print(f"\n=== MAPPING STRATEGY ===\n")
print("For each k=3 tid, find the analogous L12 tid by:")
print("1. Identifying the operation type")
print("2. Finding the same operation in L12 context")
print("3. Recording the tid")
print()
print("k=3 sliding window bases:")
sw_k3_tids = {
    'carry': 4844,
    'rms_out': 4846,
    'v_in': 4852,
    'q_in': 4854,
    'k_in': 4855,
    'cu_q': 4856,
    'cu_k': 4857,
    'attn_out': 4858,
}

for name, tid in sw_k3_tids.items():
    print(f"  {name:12s}: {tid}")

print()
print("k=12 zigzag (to be determined):")
# We know some already
zz_k12_tids = {
    'attn_out': 5347,
    'q_in': 5342,
    'k_in': 5343,
    'v_in': 5344,
    'cu_q': 5345,
    'cu_k': 5346,
}

for name, tid in zz_k12_tids.items():
    print(f"  {name:12s}: {tid}")

# Find carry and rms_out by searching backwards
print()
print("To find remaining tids, search Goal_3.lean for:")
print("  - FW_add output that feeds into RMS norm (carry)")
print("  - FW_rms_norm output that feeds into projections (rms_out)")
