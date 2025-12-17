import trainverify.core.Semantics

open Std

namespace TrainVerify

/-- Lightweight specification of a graph emitted by the generator. -/
structure GraphSpec where
  tensors : List (Nat × List Nat × Bool)
  nodes : Graph
  obsTid : Nat
  fuel : Nat
  deriving Repr

namespace GraphSpec

variable {α : Type} [Semiring α]

/-- Construct the shape map induced by the tensor metadata. -/
def shapeMap (spec : GraphSpec) : ShapeMap :=
  spec.tensors.foldl (fun m (tid, shp, _) => m.insert tid shp) {}

/-- Construct the init map induced by the tensor metadata. -/
def initMap (spec : GraphSpec) : InitMap :=
  spec.tensors.foldl (fun m (tid, _, init) => m.insert tid init) {}

/-- Runtime that replays the graph using the standard semantics. -/
def runtime (spec : GraphSpec) (env : Env α) : Runtime α :=
  Runtime.mkStandard env spec.shapeMap spec.initMap

/-- Execute the graph for the configured amount of fuel starting from an empty store. -/
def store (spec : GraphSpec) (env : Env α) : Store α :=
  (spec.runtime env).runGraph spec.nodes spec.fuel {}

/-- Fetch the observable tensor after executing the graph. -/
def output (spec : GraphSpec) (env : Env α) : Mat α :=
  (spec.store env).getD spec.obsTid []

/-- Tensor ids that appear in the metadata. -/
def tensorIds (spec : GraphSpec) : List Nat :=
  spec.tensors.map (fun (tid, _, _) => tid)

/-- All tensors referenced by a node are covered by the metadata. -/
def coversNode (spec : GraphSpec) (n : Node) : Prop :=
  List.Forall (fun tid => tid ∈ spec.tensorIds) (n.inputs ++ n.outputs)

/-- Every node is covered by the tensor metadata. -/
def wellFormed (spec : GraphSpec) : Prop :=
  List.Forall (fun n => coversNode spec n) spec.nodes

/-- Conservative fuel bound used by the interpreter. -/
def minFuel (spec : GraphSpec) : Nat :=
  5 * spec.nodes.length + 5

/-- Whether the configured fuel is at least the conservative bound. -/
def fuelSufficient (spec : GraphSpec) : Prop :=
  spec.fuel ≥ spec.minFuel

end GraphSpec

/-- Execution-plan metadata generated for each node. -/
structure ExecPlanEntry where
  idx : Nat
  node : Node
  deps : List Nat
  deriving Repr

end TrainVerify
