/- BridgeKit: 桥证明的图通用齿轮。
   sm/pm 是全局唯一的 SM/PM 计算图，下面 5 个引理只依赖它们，
   对所有 goal 桥通用。集中放这里，所有桥 import BridgeKit 复用，
   避免在 Goal4/Goal257 里各定义一份导致 import 链重复定义。
   只依赖 GeneratedData(拿 sm/pm) + Denote(底层 foldl/suffix 引理)。 -/
import denote.gpt_ly4_regen.GeneratedData
import denote.GraphGears

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedGoals

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
theorem all_initGoal_ts_not_written :
    ∀ g ∈ initGoals, ∀ n ∈ sm.nodes, g.ts ∉ n.outs := by native_decide

theorem all_initGoal_tps_not_written :
    ∀ g ∈ initGoals, ∀ tp ∈ g.tps, ∀ n ∈ pm.nodes, tp.tid ∉ n.outs := by native_decide

theorem initGoals_preserved (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks initGoals (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  initGoals_preserved_of_not_written sm pm initGoals initSM initPM
    all_initGoal_ts_not_written all_initGoal_tps_not_written hInit

end TrainVerify.Denote.GeneratedGoals
