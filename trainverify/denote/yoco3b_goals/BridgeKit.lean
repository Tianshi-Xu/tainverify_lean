/- BridgeKit: 桥证明的图通用齿轮 (YOCO 版本)。
   sm/pm 是全局唯一的 SM/PM 计算图 (from GeneratedYOCO3B)，下面 5 个引理只依赖它们，
   对所有 pattern 通用。集中放这里，所有 pattern import BridgeKit 复用。
   只依赖 GeneratedYOCO3B(拿 sm/pm) + Denote(底层 foldl/suffix 引理)。 -/
import denote.GeneratedYOCO3B

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

-- 完整图算某 tid = (前 k 节点 store 喂 applyNode 第 k 节点)，前提：第 k+1 起后缀不写 out
theorem sm_val (initSM : Store) (k : Nat) (out : Tid) (hk : k < sm.nodes.length)
    (hdrop : ∀ n ∈ sm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph sm initSM out
      = applyNode sm (denoteGraph { sm with nodes := sm.nodes.take k } initSM) sm.nodes[k] out := by
  have e1 : denoteGraph sm initSM out
      = denoteGraph { sm with nodes := sm.nodes.take (k+1) } initSM out :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM out (sm.nodes.take (k+1)) (sm.nodes.drop (k+1))
      (List.take_append_drop (k+1) sm.nodes).symm hdrop
  have hfn : applyNode { sm with nodes := sm.nodes.take (k+1) } = applyNode sm :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode { sm with nodes := sm.nodes.take k } = applyNode sm :=
    applyNode_congr_numRanks _ _ rfl
  rw [e1]
  simp only [denoteGraph, hfn, hfn']
  exact congrFun (foldl_take_succ (applyNode sm) sm.nodes initSM k hk) out

-- 后缀不写 tid 时，前缀算值 = 全图算值 (SM)
theorem sm_prefix_eq (initSM : Store) (k : Nat) (tid : Tid)
    (hdrop : ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs) :
    denoteGraph { sm with nodes := sm.nodes.take k } initSM tid = denoteGraph sm initSM tid :=
  (denoteGraph_tid_eq_of_suffix_no_writes sm initSM tid (sm.nodes.take k) (sm.nodes.drop k)
    (List.take_append_drop k sm.nodes).symm hdrop).symm

-- 前 k+1 节点 store = 前 k 节点 store 喂 applyNode 第 k 节点 (PM 单步)
theorem pm_step (initPM : Store) (k : Nat) (hk : k < pm.nodes.length) :
    denoteGraph {pm with nodes := pm.nodes.take (k+1)} initPM
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] := by
  have hfn : applyNode {pm with nodes := pm.nodes.take (k+1)} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode {pm with nodes := pm.nodes.take k} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  simp only [denoteGraph, hfn, hfn']
  exact foldl_take_succ (applyNode pm) pm.nodes initPM k hk

-- 完整图算某 tid = (前 k 节点 store 喂 applyNode 第 k 节点) (PM)
theorem pm_val (initPM : Store) (k : Nat) (out : Tid) (hk : k < pm.nodes.length)
    (hdrop : ∀ n ∈ pm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph pm initPM out
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] out := by
  have e1 : denoteGraph pm initPM out
      = denoteGraph {pm with nodes := pm.nodes.take (k+1)} initPM out :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM out (pm.nodes.take (k+1)) (pm.nodes.drop (k+1))
      (List.take_append_drop (k+1) pm.nodes).symm hdrop
  rw [e1, pm_step initPM k hk]

-- 后缀不写 tid 时，前缀算值 = 全图算值 (PM)
theorem pm_prefix_eq (initPM : Store) (k : Nat) (tid : Tid)
    (hdrop : ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs) :
    denoteGraph {pm with nodes := pm.nodes.take k} initPM tid = denoteGraph pm initPM tid :=
  (denoteGraph_tid_eq_of_suffix_no_writes pm initPM tid (pm.nodes.take k) (pm.nodes.drop k)
    (List.take_append_drop k pm.nodes).symm hdrop).symm

-- ------------------------------------------------------------------------
-- initGoals 保持：initGoals 条件是输入 tid 上的，SM/PM 都不重写输入，
-- 所以 init store 上成立 => computed store 上也成立。图通用。
-- ------------------------------------------------------------------------
-- Note (2026-07-01): YOCO's initGoal_4691.tps includes tid 11853 which IS written
-- by FW_multiref in pm — likely a generator bug where multiref outputs collide
-- with expected init tp. `all_initGoal_tps_not_written` fails as a result.
-- Pattern proofs that don't need this lemma can proceed; if patterns require
-- initGoals_preserved, we need to either fix the generator or provide a
-- narrower lemma that filters out the bad initGoal.

/-- SM side: no initGoal.ts is written by any sm node. Passes on YOCO. -/
theorem all_initGoal_ts_not_written :
    ∀ g ∈ initGoals, ∀ n ∈ sm.nodes, g.ts ∉ n.outs := by native_decide

end TrainVerify.Denote.GeneratedPatterns
