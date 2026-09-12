from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds


def test_softmax_reader_supplies_generic_ordered_output_ports(worlds):
    from Verdict.runtime_backward_softmax_reads import render_read
    for view,cells,snapshot,order,label in worlds:
        i=next(i for i,c in enumerate(cells) if c.opname.name=='BW_softmax')
        _,row=render_read(view,cells,snapshot,i,order,label)
        assert row.get('output_tids') == [row['output_tid']]
        assert row.get('output_refs') == [row['output_ref']]
