/-
Basic matrix and tensor primitives shared by the graph semantics library.
The design stays lightweight so we can instantiate it with plain nested lists.
-/

import Mathlib

open Std

universe u

namespace TrainVerify

abbrev Mat (α : Type u) := List (List α)

abbrev Store (α : Type u) := Std.HashMap Nat (Mat α)

variable {α : Type u}

/-- Create a zero-filled matrix that matches the supplied shape.
Only rank-1 and rank-2 shapes are supported by this lightweight model. -/
def zerosLike [Semiring α] : List Nat → Mat α
  | [rows, cols] => List.replicate rows (List.replicate cols 0)
  | [rows] => [List.replicate rows 0]
  | _ => []

/-- Row-major transpose for nested lists. -/
def transpose [Semiring α] : Mat α → Mat α
  | [] => []
  | row :: rows =>
      let cols := row.length
      List.range cols |>.map (fun j =>
        (row :: rows).map (fun r => r.getD j 0))

/-- Dot product on lists with zero padding. -/
def dot [Semiring α] (a b : List α) : α :=
  (List.zipWith (· * ·) a b).foldl (· + ·) 0

/-- Lightweight matrix multiplication using `transpose`. -/
def matmul [Semiring α] (a b : Mat α) : Mat α :=
  let bt := transpose b
  a.map (fun row => bt.map (dot row))

/-- Sum all entries of a matrix. -/
def sumAll [Semiring α] (m : Mat α) : α :=
  m.foldl (fun acc row => acc + row.foldl (· + ·) 0) 0

/-- Per-row sum used for some backward ops. -/
def sumRows [Semiring α] (m : Mat α) : List α :=
  m.foldl (fun acc row => if acc.length = 0 then row else List.zipWith (· + ·) acc row) []

/-- Slice matrix columns by taking `count` columns starting at `start`. -/
def sliceCols (m : Mat α) (start count : Nat) : Mat α :=
  m.map (fun row => (row.drop start).take count)

/-- Slice matrix rows by taking `count` rows starting at `start`. -/
def sliceRows (m : Mat α) (start count : Nat) : Mat α :=
  (m.drop start).take count

/-- Concatenate matrices column-wise. -/
def concatCols (ms : List (Mat α)) : Mat α :=
  match ms with
  | [] => []
  | m :: _ =>
      let rows := m.length
      List.range rows |>.map (fun i =>
        ms.foldl (fun acc mat => acc ++ mat.getD i []) ([] : List α))

/-- Concatenate matrices row-wise. -/
def concatRows (ms : List (Mat α)) : Mat α :=
  ms.foldl (· ++ ·) []

/-- Generic slice for either rows or columns. -/
def chunkBy (m : Mat α) (dim start count : Nat) : Mat α :=
  if dim = 0 then sliceRows m start count else sliceCols m start count

/-- Generic concatenation along a dimension. -/
def gatherBy (dim : Nat) (parts : List (Mat α)) : Mat α :=
  if dim = 0 then concatRows parts else concatCols parts

/-- Element-wise sum reduction used by `allReduce`. -/
def allReduce [Semiring α] : List (Mat α) → Mat α
  | [] => []
  | m0 :: rest =>
      rest.foldl
        (fun acc m =>
          List.zipWith (fun r1 r2 => List.zipWith (· + ·) r1 r2) acc m)
        m0

/-- Insert a tensor into the store under the given tensor id. -/
@[simp]
def Store.insertTensor (st : Store α) (tid : Nat) (value : Mat α) : Store α :=
  st.insert tid value

end TrainVerify
