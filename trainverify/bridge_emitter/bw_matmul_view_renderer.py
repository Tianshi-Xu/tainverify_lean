"""Compatibility entry point; query projections use the shared generic renderer."""
from __future__ import annotations


def render_closed_bw_matmul_view_segment(ir, relation, segment_id: str) -> str:
    try:
        from .bw_matmul_query_renderer import render_closed_bw_matmul_query_segment
    except ImportError:
        from bw_matmul_query_renderer import render_closed_bw_matmul_query_segment
    return render_closed_bw_matmul_query_segment(ir, relation, segment_id)
