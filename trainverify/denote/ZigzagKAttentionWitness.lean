import denote.ZigzagKAttention

/-! Kernel audit entry point for the arbitrary-K attention relation candidate.
The output's actual chunk witnesses are constructed in `attention_chunks` and
passed to `ZigzagKRel.of_sharded`; no abstract reconstruction oracle is assumed. -/

open TrainVerify.Denote.RelationCompiler

#check ShardedRel.attention_chunks
#check ZigzagKRel.attn_zigzag_sharded_kv_single
#print axioms ShardedRel.attention_chunks
#print axioms ZigzagKRel.attn_zigzag_sharded_kv_single
