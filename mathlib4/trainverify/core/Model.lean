/-
Core graph data structures shared by the semantic development.
Nodes refer to tensor ids via natural numbers to stay close to the runtime format.
-/

import trainverify.core.Primitives

open Std

universe u

namespace TrainVerify

/-- Lightweight catalogue of operations a node can execute.
This set mirrors the operators we used in the SM/PM comparison and can be
extended later by adding constructors. -/
inductive Op where
  | dataloader
  | fwLinear
  | bwLinear
  | fwSum
  | bwSum
  | chunk (dim idx : Nat)
  | allReduce
  | allGather (dim : Nat)
  | custom (tag : String)
  deriving DecidableEq, Repr

/-- A node records the operation tag plus input and output tensor ids. -/
structure Node where
  op : Op
  inputs : List Nat
  outputs : List Nat
  deriving Repr

abbrev Graph := List Node

end TrainVerify
