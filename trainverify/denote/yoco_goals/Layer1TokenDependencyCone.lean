import denote.yoco_goals.Layer1DistributedMigration

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem dreshape (g : GraphDecl) (init : Store) (k rank i o hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = {rank:=rank, op:="OpName.FW_reshape", ins:=[i], outs:=[o], params:=hd::tl})
    (hdn : ∀ n ∈ g.nodes.drop (k+1), n.outs ≠ []) (hdw : ∀ n ∈ g.nodes.drop (k+1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ []) (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd::tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd::tl)) hk hn (by simp)
    (fun s => applyNode_fw_reshape_out g s rank i o (hd::tl)) hdn hdw hpn hpw

 theorem recon_intermediateGoal_4751_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4751 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4750_distributed initSM initPM hSM hPM hInit
  have hsh := h.2.1
  simp only [intermediateGoal_4750, List.map, List.cons.injEq, and_true] at hsh
  have hs0 := hsh.1; have hs1 := hsh.2
  have hv0 := h.2.2
  rw [reconstructForGoal_of_not_replicated intermediateGoal_4750 pm.numRanks _ rfl] at hv0
  simp only [intermediateGoal_4750, List.map] at hv0
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ [] (by rw [hs0]; decide)] at hv0
  have rs := dreshape sm initSM 49 0 4750 4751 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := dreshape pm initPM 146 0 7623 7625 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := dreshape pm initPM 147 1 7624 7626 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4751 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7625, denoteGraphDistributed pm initPM 7626] := by
    rw [rs, hv0, r0, r1]; exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs0 hs1
  have hss : (denoteGraphDistributed sm initSM 4751).shape = [4096,1024] := by rw [rs]; rfl
  have hp0 : (denoteGraphDistributed pm initPM 7625).shape = [2048,1024] := by rw [r0]; rfl
  have hp1 : (denoteGraphDistributed pm initPM 7626).shape = [2048,1024] := by rw [r1]; rfl
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_4751 4751 7625 7626 [4096,1024] [2048,1024]
    rfl rfl rfl rfl rfl rfl (by decide) hv hss hp0 hp1

 theorem recon_intermediateGoal_4752_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4752 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4751_distributed initSM initPM hSM hPM hInit
  have hsh := h.2.1
  simp only [intermediateGoal_4751, List.map, List.cons.injEq, and_true] at hsh
  have hs0 := hsh.1; have hs1 := hsh.2
  have hv0 := h.2.2
  rw [reconstructForGoal_of_not_replicated intermediateGoal_4751 pm.numRanks _ rfl] at hv0
  simp only [intermediateGoal_4751, List.map] at hv0
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ [] (by rw [hs0]; decide)] at hv0
  have hs : (denoteGraphDistributed sm initSM 4751).shape = [4096,1024] := h.1
  have rs := dreshape sm initSM 50 0 4751 4752 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := dreshape pm initPM 148 0 7625 7631 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := dreshape pm initPM 149 1 7626 7632 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce2 pm initPM 150
    {rank:=0,op:="OpName.AllGatherPrim",ins:=[7631,7632],outs:=[4752],params:=[0]}
    7631 7632 4752 (fun a b => allGatherPrimDimN 0 2 0 [a,b]) (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_allGatherPrimDimN_out_thm pm s 0 [7631,7632] 4752 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4752 = denoteGraphDistributed pm initPM 4752 := by
    rw [rs, fw_view_id_shape [4096,1024] _ hs, rp, r0, fw_view_id_shape [2048,1024] _ hs0,
      r1, fw_view_id_shape [2048,1024] _ hs1, hv0, show pm.numRanks = 2 from rfl]
  have hso : (denoteGraphDistributed sm initSM 4752).shape = [4096,1024] := by
    rw [rs, fw_view_id_shape [4096,1024] _ hs]; exact hs
  exact wrap_1tp_gen _ _ intermediateGoal_4752 4752 [4096,1024] rfl rfl rfl rfl rfl rfl hv hso

private theorem dweight_value (initSM initPM : Store) (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hg : gW ∈ initGoals) (w : Tid)
    (htp : gW.tps = [{rank:=0,tid:=w}]) (hgd : gW.gatherDim=0) (hr : gW.replicated=false) (hts : gW.ts=w)
    (hs : ∀ n ∈ sm.nodes, w ∉ n.outs) (hp : ∀ n ∈ pm.nodes, w ∉ n.outs) :
    denoteGraphDistributed sm initSM w = denoteGraphDistributed pm initPM w :=
  distributed_init_singleton_value initSM initPM hInit gW hg w htp hgd hr hts
    layer1_sm_nodes_nonempty hs layer1_pm_nodes_nonempty hp

 theorem recon_intermediateGoal_4754_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4754 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4752_distributed initSM initPM hSM hPM hInit
  have hv0 := oneTp_valeq intermediateGoal_4752 _ _ 4752 rfl rfl rfl rfl h
  have hs0 : (denoteGraphDistributed sm initSM 4752).shape=[4096,1024] := h.1
  have hw := dweight_value initSM initPM hInit initGoal_4753 (by native_decide) 4753 rfl rfl rfl rfl
    (by native_decide) (by native_decide)
  have hsw := distributed_init_singleton_shape initSM initPM hInit initGoal_4753 (by native_decide)
    4753 [1024,1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rs := distributed_reduce2 sm initSM 51
    {rank:=0,op:="OpName.FW_mix_precision_linear",ins:=[4752,4753],outs:=[4754]} 4752 4753 4754 fw_linear
    (by native_decide) (by native_decide) (by decide) (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4752 4753 4754)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce2 pm initPM 152
    {rank:=1,op:="OpName.FW_mix_precision_linear",ins:=[4752,4753],outs:=[4754]} 4752 4753 4754 fw_linear
    (by native_decide) (by native_decide) (by decide) (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4752 4753 4754)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4754 = denoteGraphDistributed pm initPM 4754 := by rw [rs,rp,hv0,hw]
  have hs : (denoteGraphDistributed sm initSM 4754).shape=[4096,1024] := by
    rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ hs0 hsw
  exact wrap_1tp_gen _ _ intermediateGoal_4754 4754 [4096,1024] rfl rfl rfl rfl rfl rfl hv hs

 theorem recon_intermediateGoal_4755_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4755 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4754_distributed initSM initPM hSM hPM hInit
  have hv0 := oneTp_valeq intermediateGoal_4754 _ _ 4754 rfl rfl rfl rfl h
  have rs := distributed_reduce1 sm initSM 52
    {rank:=0,op:="OpName.FW_view",ins:=[4754],outs:=[4755],params:=[4096,1024]}
    4754 4755 (fw_view [4096,1024]) (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4754 4755)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce1 pm initPM 154
    {rank:=1,op:="OpName.FW_view",ins:=[4754],outs:=[4755],params:=[4096,1024]}
    4754 4755 (fw_view [4096,1024]) (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_view_out pm s 1 4096 [1024] 4754 4755)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4755 = denoteGraphDistributed pm initPM 4755 := by rw [rs,rp,hv0]
  have hs : (denoteGraphDistributed sm initSM 4755).shape=[4096,1024] := by rw [rs]; rfl
  exact wrap_1tp_gen _ _ intermediateGoal_4755 4755 [4096,1024] rfl rfl rfl rfl rfl rfl hv hs

 theorem recon_intermediateGoal_4756_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4756 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4755_distributed initSM initPM hSM hPM hInit
  have hv0 := oneTp_valeq intermediateGoal_4755 _ _ 4755 rfl rfl rfl rfl h
  have hs0 : (denoteGraphDistributed sm initSM 4755).shape=[4096,1024] := h.1
  have rs := distributed_reduce1 sm initSM 53 {rank:=0,op:="OpName.FW_float",ins:=[4755],outs:=[4756]}
    4755 4756 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_float_out sm s 0 4755 4756 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce1 pm initPM 156 {rank:=1,op:="OpName.FW_float",ins:=[4755],outs:=[4756]}
    4755 4756 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_float_out pm s 1 4755 4756 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs rp
  have hv : denoteGraphDistributed sm initSM 4756 = denoteGraphDistributed pm initPM 4756 := by rw [rs,rp,hv0]
  have hs : (denoteGraphDistributed sm initSM 4756).shape=[4096,1024] := by rw [rs]; exact hs0
  exact wrap_1tp_gen _ _ intermediateGoal_4756 4756 [4096,1024] rfl rfl rfl rfl rfl rfl hv hs

 theorem recon_intermediateGoal_4757_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4757 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h56 := recon_intermediateGoal_4756_distributed initSM initPM hSM hPM hInit
  have hv56 := oneTp_valeq intermediateGoal_4756 _ _ 4756 rfl rfl rfl rfl h56
  have hs56 : (denoteGraphDistributed sm initSM 4756).shape=[4096,1024] := h56.1
  have h36 := recon_intermediateGoal_4736_distributed initSM initPM hSM hPM hInit
  have hv36 := oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl h36
  have hs36 : (denoteGraphDistributed sm initSM 4736).shape=[4096,1024] := h36.1
  have ss := distributed_reduce1 sm initSM 41
    {rank:=0,op:="OpName.FW_multiref",ins:=[4736],outs:=[7435,7439],params:=[2]}
    4736 7439 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' sm s 0 4736 7435 7439 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have sp := distributed_reduce1 pm initPM 125
    {rank:=1,op:="OpName.FW_multiref",ins:=[4736],outs:=[14668,14672],params:=[2]}
    4736 14672 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 1 4736 14668 14672 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ss sp
  have rs := distributed_reduce2 sm initSM 54 {rank:=0,op:="OpName.FW_add",ins:=[7439,4756],outs:=[4757]}
    7439 4756 4757 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_add2_out sm s 0 7439 4756 4757)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce2 pm initPM 158 {rank:=1,op:="OpName.FW_add",ins:=[14672,4756],outs:=[4757]}
    14672 4756 4757 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_add2_out pm s 1 14672 4756 4757)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4757 = denoteGraphDistributed pm initPM 4757 := by rw [rs,rp,ss,sp,hv36,hv56]
  have hs : (denoteGraphDistributed sm initSM 4757).shape=[4096,1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096,1024] (by rw [ss]; exact hs36) hs56
  exact wrap_1tp_gen _ _ intermediateGoal_4757 4757 [4096,1024] rfl rfl rfl rfl rfl rfl hv hs

 theorem recon_intermediateGoal_4759_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4759 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4757_distributed initSM initPM hSM hPM hInit
  have hv0 := oneTp_valeq intermediateGoal_4757 _ _ 4757 rfl rfl rfl rfl h
  have hs0 : (denoteGraphDistributed sm initSM 4757).shape=[4096,1024] := h.1
  have ss := distributed_reduce1 sm initSM 55 {rank:=0,op:="OpName.FW_multiref",ins:=[4757],outs:=[7456,7460],params:=[2]}
    4757 7456 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_first_out sm s 0 4757 7456 7460)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have sp := distributed_reduce1 pm initPM 160 {rank:=1,op:="OpName.FW_multiref",ins:=[4757],outs:=[11889,11890],params:=[2]}
    4757 11889 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_first_out pm s 1 4757 11889 11890)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ss sp
  have hw := dweight_value initSM initPM hInit initGoal_4758 (by native_decide) 4758 rfl rfl rfl rfl
    (by native_decide) (by native_decide)
  have rs := distributed_reduce2 sm initSM 56 {rank:=0,op:="OpName.FW_rms_norm",ins:=[7456,4758],outs:=[4759]}
    7456 4758 4759 fw_rms_norm (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7456 4758 4759)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp := distributed_reduce2 pm initPM 163 {rank:=1,op:="OpName.FW_rms_norm",ins:=[11889,4758],outs:=[4759]}
    11889 4758 4759 fw_rms_norm (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm s 1 11889 4758 4759)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 4759 = denoteGraphDistributed pm initPM 4759 := by rw [rs,rp,ss,sp,hv0,hw]
  have hs : (denoteGraphDistributed sm initSM 4759).shape=[4096,1024] := by
    rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ss]; exact hs0)
  exact wrap_1tp_gen _ _ intermediateGoal_4759 4759 [4096,1024] rfl rfl rfl rfl rfl rfl hv hs

#print axioms recon_intermediateGoal_4759_distributed

 theorem recon_intermediateGoal_7471_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7471 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := recon_intermediateGoal_4759_distributed initSM initPM hSM hPM hInit
  have hv0 := oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h
  have hs0 : (denoteGraphDistributed sm initSM 4759).shape=[4096,1024] := h.1
  have ss := distributed_reduce1 sm initSM 57
    {rank:=0,op:="OpName.FW_multiref",ins:=[4759],outs:=[7467,7471,7475,7479,7483],params:=[5]}
    4759 7471 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have sp := distributed_reduce1 pm initPM 166
    {rank:=1,op:="OpName.FW_multiref",ins:=[4759],outs:=[11903,11904,11905,11906,11907],params:=[5]}
    4759 11904 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ss sp
  have c0 := distributed_reduce1 pm initPM 168
    {rank:=0,op:="OpName.ChunkPrim",ins:=[11904],outs:=[11977],params:=[0]}
    11904 11977 (chunkPrimDimN 0 pm.numRanks 0) (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_chunkPrimDimN_out pm s 0 11904 11977 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := distributed_reduce1 pm initPM 173
    {rank:=1,op:="OpName.ChunkPrim",ins:=[11904],outs:=[11978],params:=[0]}
    11904 11978 (chunkPrimDimN 0 pm.numRanks 1) (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_chunkPrimDimN_out pm s 1 11904 11978 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp : (denoteGraphDistributed pm initPM 11904).shape=[4096,1024] := by rw [sp, ← hv0]; exact hs0
  have hp0 : (denoteGraphDistributed pm initPM 11977).shape=[2048,1024] := by
    rw [c0, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096,1024] hp (by native_decide)]; rfl
  have hp1 : (denoteGraphDistributed pm initPM 11978).shape=[2048,1024] := by
    rw [c1, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096,1024] hp (by native_decide)]; rfl
  have hv : denoteGraphDistributed sm initSM 7471 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 11977,denoteGraphDistributed pm initPM 11978] := by
    rw [ss,hv0,←sp,c0,c1,show pm.numRanks=2 from rfl]
    exact (allGather0_reconstruct_chunks_2d 2048 1024 (by omega) (by omega) _ hp).symm
  have hs : (denoteGraphDistributed sm initSM 7471).shape=[4096,1024] := by rw [ss,hv0,←sp]; exact hp
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_7471 7471 11977 11978 [4096,1024] [2048,1024]
    rfl rfl rfl rfl rfl rfl (by decide) hv hs hp0 hp1

#print axioms recon_intermediateGoal_7471_distributed

end TrainVerify.Denote.GeneratedPatterns
