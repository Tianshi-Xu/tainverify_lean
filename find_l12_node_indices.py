#!/usr/bin/env python3
"""
Find node indices for L12 tids in Goal_3.lean.

This helps determine the correct arguments for DenoteUnfoldGeneric.dstep*.
"""

import re
import sys

def find_node_indices(goal3_file, target_tids):
    """Find node indices for given output tids."""
    
    with open(goal3_file, 'r') as f:
        lines = f.readlines()
    
    # Find where sm_goal_3.nodes starts
    in_sm_nodes = False
    node_index = 0
    results = {}
    
    for i, line in enumerate(lines):
        # Detect start of sm_goal_3.nodes
        if 'def sm_goal_3.nodes' in line:
            in_sm_nodes = True
            continue
        
        if not in_sm_nodes:
            continue
        
        # Detect end of nodes list
        if line.strip().startswith(']') and 'def sm_goal_3.initEnv' in lines[i+1] if i+1 < len(lines) else False:
            break
        
        # Parse node declarations
        if 'rank :=' in line:
            # Extract outs field
            match = re.search(r'outs := \[([^\]]+)\]', line)
            if match:
                outs_str = match.group(1)
                outs = [int(x.strip()) for x in outs_str.split(',')]
                
                for tid in outs:
                    if tid in target_tids:
                        results[tid] = {
                            'index': node_index,
                            'line_num': i + 1,
                            'line': line.strip()
                        }
            
            node_index += 1
    
    return results

def main():
    if len(sys.argv) < 2:
        print("Usage: find_l12_node_indices.py <Goal_3.lean>")
        sys.exit(1)
    
    goal3_file = sys.argv[1]
    
    # L12 tids we care about
    l12_tids = [
        5330,  # carry
        5332,  # RMS norm main
        5340,  # RMS norm Q-path
        5342,  # Q
        5343,  # K
        5344,  # V
        5347,  # attention output
        8007,  # multiref output (input to RMS norm)
        8011,  # multiref output
        8015,  # multiref output
        8019,  # multiref output
    ]
    
    results = find_node_indices(goal3_file, l12_tids)
    
    print("L12 Node Indices:")
    print("=" * 70)
    for tid in sorted(results.keys()):
        info = results[tid]
        print(f"TID {tid}: node index {info['index']}, line {info['line_num']}")
        print(f"  {info['line']}")
        print()
    
    # Save to file for easy reference
    with open('/tmp/l12_node_indices.txt', 'w') as f:
        for tid in sorted(results.keys()):
            info = results[tid]
            f.write(f"{tid}\t{info['index']}\n")
    
    print(f"Saved mapping to /tmp/l12_node_indices.txt")

if __name__ == "__main__":
    main()
