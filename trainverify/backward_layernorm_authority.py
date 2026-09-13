"""Authenticate original affine last-axis BW_layernorm, before rendering reads."""
from trainverify.backward_linear_authority import _ir_identity
from Verdict.runtime_lineage import _same_typed


def _fail(reason):
    raise ValueError('bw-layernorm '+reason)


def bind(cells,source_index):
    from nnscaler.ir.operator import IRBpOperation
    if type(source_index) is not int or not 0<=source_index<len(cells): _fail('invalid source index')
    cell=cells[source_index]
    if not isinstance(cell.ir,IRBpOperation) or cell.opname.name!='BW_layernorm':
        _fail('original typed backward operation required')
    paired=[(i,c) for i,c in enumerate(cells) if c.ir is cell.ir.mirror
            and (c.node.wtype,c.rank,c.mb)==(cell.node.wtype,cell.rank,cell.mb)]
    if len(paired)!=1 or paired[0][0]>=source_index: _fail('original forward mirror order/identity mismatch')
    fi,fw=paired[0]
    if fw.opname.name!='FW_layernorm' or fw.ir.signature!='nnscaler.runtime.function.layer_norm':
        _fail('original forward function/opcode mismatch')
    if cell.ir.signature!='torch.autograd.grad': _fail('original backward function mismatch')
    if (len(cell.inputs)!=4 or len(cell.outputs)!=3 or len(cell._input_irs)!=4 or len(cell._output_irs)!=3
            or len(fw.inputs)!=3 or len(fw.outputs)!=1 or len(fw._input_irs)!=3 or len(fw._output_irs)!=1):
        _fail('complete affine ordered ports required')
    if not _same_typed([tuple(r) for r in cell.inputs[1:]],[tuple(r) for r in fw.inputs]):
        _fail('saved primal fullref/version mismatch')
    for obj,name in ((cell,'BW.'+fw.ir.name),(fw,fw.ir.name)):
        if not _same_typed(tuple(obj.node),(obj.wtype.value,obj.rank,obj.mb,obj.ir.cid,name)):
            _fail('original typed node/IR identity mismatch')
        kwargs=dict(obj.kwargs)
        if set(kwargs)-{'normalized_shape','eps','__consts'} or kwargs.get('__consts',[])!=[]:
            _fail('unsupported source kwargs')
        kwargs.pop('__consts',None)
        raw=dict(obj.ir.kwargs); raw.pop('__consts',None)
        if not _same_typed(kwargs,raw): _fail('original IR/cell kwargs mismatch')
        eps=kwargs.get('eps',1e-5); norm=kwargs.get('normalized_shape')
        if type(eps) not in (float,int) or eps!=1e-5: _fail('Denote requires source epsilon 1e-5')
        x=cell._input_irs[1]
        if (type(norm) not in (tuple,list) or len(norm)!=1 or type(norm[0]) is not int
                or norm[0]<=0 or not x.shape or norm[0]!=x.shape[-1]):
            _fail('positive last-axis normalization required')
        for refs,irs in ((obj.inputs,obj._input_irs),(obj.outputs,obj._output_irs)):
            for ref,ir in zip(refs,irs,strict=True):
                expected=(obj.node.wtype,obj.rank,-1 if ir.is_attr() else obj.mb,ir.tid)
                if not _same_typed(tuple(ref)[:4],expected) or type(ref.v) is not int or ref.v<0:
                    _fail('ordered source fullref/IR identity mismatch')
    fwi,fwo=list(fw.ir.inputs()),list(fw.ir.outputs())
    bwi=list(cell.ir.inputs())+fwi; bwo=list(cell.ir.outputs())
    if len(fwi)!=3 or len(fwo)!=1 or len(bwi)!=4 or len(bwo)!=3: _fail('original mirror arity mismatch')
    for actual,expected in ((cell._input_irs,bwi),(cell._output_irs,bwo),(fw._input_irs,fwi),
                            (fw._output_irs,fwo),([cell._input_irs[0]],[fwo[0].grad]),
                            (cell._output_irs,[t.grad for t in fwi])):
        if not _same_typed([_ir_identity(t) for t in actual],[_ir_identity(t) for t in expected]):
            _fail('original mirror saved/gradient metadata mismatch')
    for ref,ir in zip(cell.inputs,cell._input_irs,strict=True):
        if ref.v==0 and not (ir.is_attr() is True and ir.is_grad() is False):
            _fail('external activation/cotangent lacks original writer authority')
        writers=[c for c in cells[:source_index] if any(_same_typed(tuple(r),tuple(ref)) for r in c.outputs)]
        if ref.v!=0 and len(writers)!=1: _fail('input writer/version missing/ambiguous')
    watched=[tuple(r) for r in (*cell.inputs,*cell.outputs)]
    if any(_same_typed(tuple(r),key) for later in cells[source_index+1:] for r in later.outputs for key in watched):
        _fail('input/output fullref suffix overwrite')
    g,x,gamma,beta=cell._input_irs; d=x.shape[-1]
    if (any(type(n) is not int or n<=0 for n in x.shape) or tuple(g.shape)!=tuple(x.shape)
            or tuple(gamma.shape)!=(d,) or tuple(beta.shape)!=(d,)
            or [tuple(z.shape) for z in cell._output_irs]!=[tuple(x.shape),(d,),(d,)]
            or tuple(fw._output_irs[0].shape)!=tuple(x.shape)):
        _fail('affine normalization/gradient shapes mismatch')
    return dict(source_index=source_index,fw_source_index=fi,bw_node=list(cell.node),fw_node=list(fw.node),
                inputs=[list(r) for r in cell.inputs],outputs=[list(r) for r in cell.outputs],
                input_roles=['cotangent','saved_input','saved_gamma','saved_beta'],
                output_roles=['dx','dgamma','dbeta'],epsilon=1e-5,normalized_shape=[d],
                obligations=['original cotangent reconstruction','forward saved-input values for dx/dgamma',
                             'parameter values and original reduction ownership'],
                proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
