"""Compatibility entry point for the generic head-sharded matmul renderer."""


def render_closed_paired_batch_bw_matmul_segment(ir, relation, segment_id):
    try:
        from .bw_matmul_head_renderer import render_closed_bw_matmul_head_segment
    except ImportError:
        from bw_matmul_head_renderer import render_closed_bw_matmul_head_segment
    return render_closed_bw_matmul_head_segment(ir, relation, segment_id)
