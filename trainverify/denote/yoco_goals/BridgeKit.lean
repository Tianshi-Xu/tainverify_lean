/- BridgeKit: 桥证明的图通用齿轮 (YOCO 版本)。
   sm/pm 是全局唯一的 SM/PM 计算图 (from GeneratedYOCOMoE)，下面 5 个引理只依赖它们，
   对所有 pattern 通用。集中放这里，所有 pattern import BridgeKit 复用。
   只依赖 GeneratedYOCOMoE(拿 sm/pm) + Denote(底层 foldl/suffix 引理)。 -/
import denote.GeneratedYOCOMoE
import denote.GraphGears

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

-- 完整图算某 tid = (前 k 节点 store 喂 applyNode 第 k 节点)，前提：第 k+1 起后缀不写 out
theorem sm_val (initSM : Store) (k : Nat) (out : Tid) (hk : k < sm.nodes.length)
    (hdrop : ∀ n ∈ sm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph sm initSM out
      = applyNode sm (denoteGraph { sm with nodes := sm.nodes.take k } initSM) sm.nodes[k] out :=
  denoteGraph_val_at_node sm initSM k out hk hdrop

-- 后缀不写 tid 时，前缀算值 = 全图算值 (SM)
theorem sm_prefix_eq (initSM : Store) (k : Nat) (tid : Tid)
    (hdrop : ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs) :
    denoteGraph { sm with nodes := sm.nodes.take k } initSM tid = denoteGraph sm initSM tid :=
  denoteGraph_prefix_eq sm initSM k tid hdrop

-- 前 k+1 节点 store = 前 k 节点 store 喂 applyNode 第 k 节点 (PM 单步)
theorem pm_step (initPM : Store) (k : Nat) (hk : k < pm.nodes.length) :
    denoteGraph {pm with nodes := pm.nodes.take (k+1)} initPM
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] :=
  denoteGraph_step pm initPM k hk

-- 完整图算某 tid = (前 k 节点 store 喂 applyNode 第 k 节点) (PM)
theorem pm_val (initPM : Store) (k : Nat) (out : Tid) (hk : k < pm.nodes.length)
    (hdrop : ∀ n ∈ pm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph pm initPM out
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] out :=
  denoteGraph_val_at_node pm initPM k out hk hdrop

-- 后缀不写 tid 时，前缀算值 = 全图算值 (PM)
theorem pm_prefix_eq (initPM : Store) (k : Nat) (tid : Tid)
    (hdrop : ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs) :
    denoteGraph {pm with nodes := pm.nodes.take k} initPM tid = denoteGraph pm initPM tid :=
  denoteGraph_prefix_eq pm initPM k tid hdrop

-- ------------------------------------------------------------------------
-- initGoals 保持：initGoals 条件是输入 tid 上的，SM/PM 都不重写输入，
-- 所以 init store 上成立 => computed store 上也成立。图通用。
-- ------------------------------------------------------------------------
-- Note (2026-07-14): earlier comment about `initGoal_4691.tps` including tid
-- 11853 was stale — the emitter has since been fixed. Both
-- `all_initGoal_ts_not_written` and `all_initGoal_tps_not_written` now pass
-- via native_decide on the current YOCO generator output.

/-- SM side: no initGoal.ts is written by any sm node. Passes on YOCO. -/
theorem all_initGoal_ts_not_written :
    ∀ g ∈ initGoals, ∀ n ∈ sm.nodes, g.ts ∉ n.outs := by native_decide

/-- PM side: no initGoal.tp.tid is written by any pm node. -/
theorem all_initGoal_tps_not_written :
    ∀ g ∈ initGoals, ∀ tp ∈ g.tps, ∀ n ∈ pm.nodes, tp.tid ∉ n.outs := by native_decide

/-- Key lemma for non-base bridges: initGoals hold on `initStores` ⇒ they hold
    on the computed stores `denoteGraph sm initSM / denoteGraph pm initPM`,
    because neither graph rewrites any tid appearing in an initGoal. -/
theorem initGoals_preserved (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks initGoals (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  initGoals_preserved_of_not_written sm pm initGoals initSM initPM
    all_initGoal_ts_not_written all_initGoal_tps_not_written hInit

-- ------------------------------------------------------------------------
-- Prefix-of-prefix reduction: computing on `take K` graph but only needing tid
-- written at position k < K, and no nodes in K's suffix write it.
-- ------------------------------------------------------------------------
theorem pm_val_prefix (initPM : Store) (K k : Nat)
    (hKlen : K ≤ pm.nodes.length) (hk : k < K)
    (out : Tid)
    (hdrop : ∀ n ∈ (pm.nodes.take K).drop (k+1), out ∉ n.outs) :
    denoteGraph {pm with nodes := pm.nodes.take K} initPM out
      = applyNode pm
          (denoteGraph {pm with nodes := (pm.nodes.take K).take k} initPM)
          ((pm.nodes.take K)[k]'(by change k < (pm.nodes.take K).length; rw [List.length_take]; omega)) out := by
  set g' : GraphDecl := {pm with nodes := pm.nodes.take K} with hg'
  have hg'_len : k < g'.nodes.length := by
    change k < (pm.nodes.take K).length
    rw [List.length_take]; omega
  have e1 : denoteGraph g' initPM out
      = denoteGraph {g' with nodes := g'.nodes.take (k+1)} initPM out :=
    denoteGraph_tid_eq_of_suffix_no_writes g' initPM out (g'.nodes.take (k+1))
      (g'.nodes.drop (k+1)) (List.take_append_drop (k+1) g'.nodes).symm hdrop
  have hfn : applyNode {g' with nodes := g'.nodes.take (k+1)} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode {g' with nodes := g'.nodes.take k} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  rw [e1]
  simp only [denoteGraph, hfn, hfn']
  exact congrFun (foldl_take_succ (applyNode pm) g'.nodes initPM k hg'_len) out

-- ------------------------------------------------------------------------
-- Universal helper lemmas (used by auto-generated bridges).
-- These match gpt_ly4_regen's SpikeBridge counterparts; kept here so yoco
-- bridges can rely on BridgeKit alone.
-- ------------------------------------------------------------------------

/-- `shapeEnvOfList` lookup success ⇒ membership. -/
theorem mem_of_shapeEnvOfList_eq_some {xs : List (Tid × Shape)} {tid sh}
    (h : shapeEnvOfList xs tid = some sh) : (tid, sh) ∈ xs :=
  shapeEnvOfList_mem_of_eq_some h

/-- Sub-env weakening for `StoreShapesHold`. -/
theorem storeShapes_weaken {init : Store} {small big : List (Tid × Shape)}
    (hsub : ∀ p ∈ small, shapeEnvOfList big p.1 = some p.2)
    (hbig : StoreShapesHold init (shapeEnvOfList big)) :
    StoreShapesHold init (shapeEnvOfList small) :=
  storeShapesHold_weaken hsub hbig

end TrainVerify.Denote.GeneratedPatterns
