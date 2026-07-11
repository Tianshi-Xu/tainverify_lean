#!/usr/bin/env python3
"""
Generate L12 attention theorem by transforming L3 theorem with tid substitutions.

This automates the tedious manual substitution process described in PROMPT-L12-STATUS.md.
"""

import re
import sys

# TID mapping from L3 (k=3) to L12 (k=12)
# From PROMPT-L12-STATUS.md section 3
TID_MAP = {
    # SM side
    "4844": "5330",  # carry input
    "4846": "5332",  # RMS norm out (main)
    "4852": "5344",  # V input
    "4854": "5342",  # Q input
    "4855": "5343",  # K input  
    "4856": "5345",  # cu_seqlens Q
    "4857": "5346",  # cu_seqlens K
    "4858": "5347",  # Attention output
    
    # PM side (r0)
    "7991": "9659",  # Q input (r0)
    "7993": "5343",  # K input (shared, actually should stay same!)
    "7979": "5344",  # V input (shared, actually should stay same!)
    "7995": "9687",  # Attn output (r0)
    "7996": "9688",  # Attn output (r1)
    
    # PM side (r1)
    "7992": "9660",  # Q input (r1)
    
    # Note: Some PM tids may be shared with SM (like K/V inputs 5343/5344)
    # Need to be careful about context
}

# Additional mappings needed (will extract from examining L3 proof)
# These are helper tids, multiref outputs, etc.

def transform_l3_to_l12(l3_code: str) -> str:
    """Transform L3 theorem code to L12 by substituting tids and op names."""
    
    result = l3_code
    
    # Step 1: Replace theorem name
    result = result.replace("sm_pm_attention_L3_commute", "sm_pm_attention_L12_commute")
    
    # Step 2: Replace op names (sliding_window -> zigzag)
    result = result.replace("_sliding_window_", "_zigzag_")
    result = result.replace("OpName.FW_attn_sliding_window", "OpName.FW_attn_zigzag")
    
    # Step 3: Replace params ([..., 512] -> [..., 0])
    result = re.sub(r'\[16, 4, 64, 64, 1, 512\]', '[16, 4, 64, 64, 1, 0]', result)
    
    # Step 4: Replace node identifiers (nSM_3 -> nSM_12, etc.)
    result = result.replace("nSM_3", "nSM_12")
    result = result.replace("nR0_3", "nR0_12")
    result = result.replace("nR1_3", "nR1_12")
    result = result.replace("buddy_sm_3", "buddy_sm_12")
    result = result.replace("buddy_r0_3", "buddy_r0_12")
    result = result.replace("buddy_r1_3", "buddy_r1_12")
    
    # Step 5: Replace dependency theorem names (L3 -> L12)
    result = result.replace("_L3_commute", "_L12_commute")
    
    # Step 6: Replace TIDs (this is the critical part)
    # Need to be careful about context - some tids appear in multiple roles
    #  For now, do direct substitution
    for old_tid, new_tid in sorted(TID_MAP.items(), key=lambda x: -len(x[0])):
        # Use word boundaries to avoid partial matches
        result = re.sub(r'\b' + old_tid + r'\b', new_tid, result)
    
    # Step 7: Update take counts (node indices)
    # L3: SM take 47, PM take 139/140
    # L12: SM take 504/505, PM take 1970/1971/1972
    result = re.sub(r'\btake 47\b', 'take 504', result)
    result = re.sub(r'\btake 139\b', 'take 1970', result)
    result = re.sub(r'\btake 140\b', 'take 1971', result)
    
    return result

def main():
    if len(sys.argv) != 3:
        print("Usage: generate_l12_from_l3.py <input_l3_theorem.lean> <output_l12_theorem.lean>")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2]
    
    with open(input_file, 'r') as f:
        l3_code = f.read()
    
    l12_code = transform_l3_to_l12(l3_code)
    
    with open(output_file, 'w') as f:
        f.write(l12_code)
    
    print(f"Generated L12 theorem in {output_file}")
    print("WARNING: This is a mechanical transformation. You MUST:")
    print("  1. Review all TID substitutions carefully")
    print("  2. Verify take counts are correct")
    print("  3. Check that shared tids (K/V inputs) are handled correctly")
    print("  4. Build and fix any type errors")

if __name__ == "__main__":
    main()
