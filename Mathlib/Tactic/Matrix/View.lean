/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Util.Qq

/-!
# Views of matrix terms

`MatrixView` is an alternative inductive type of matrices, whose constructors build a matrix from
the rows of a list literal or from a function of its indices. `MatrixView.toMatrix` is the matrix a
view builds, and `MatrixViewOf.parse` finds a view of a given term with a proof that it builds it.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

/-- Two forms of one list-based matrix literal. This makes the argument list more succinct when a
function needs several representations. -/
structure ListMatrixLit {u : Level} (α : Q(Type u)) (m n : Nat) where
  /-- The list literal of `rows`. -/
  lit : Q(List (List $α))
  /-- The rows of the matrix. -/
  rows : List (List Q($α))

/-- The `ListMatrixLit` of the matrix with rows `rows`. -/
def ListMatrixLit.ofArray {u : Level} {α : Q(Type u)} (m n : Nat)
    (rows : Array (Array Q($α))) : ListMatrixLit α m n :=
  let rows := rows.toList.map Array.toList
  let lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (rows.map mkListLitQ)
  { lit, rows }

/-- Alternative constructors of matrices with rows indexed by `m` and columns by `n`. -/
inductive MatrixView {u : Level} (α : Q(Type u)) (m n : Q(Type)) where
  /-- The matrix built by `ofLists` from the list-based literal `A`, when `m` is `Fin k` and `n`
  is `Fin l`. -/
  | literal (zα : Q(Zero $α)) (k l : Nat) (hm : $m =Q Fin $k) (hn : $n =Q Fin $l)
      (A : ListMatrixLit α k l)
  /-- The matrix built by `Matrix.of` from the function `f`. -/
  | functional (f : Q($m → $n → $α))

/-- The matrix that the view `v` builds. The body is exposed so that a consumer's quotations see
`toMatrix` of a constructor reduce to its matrix. -/
@[expose] def MatrixView.toMatrix {u : Level} {α : Q(Type u)} {m n : Q(Type)}
    (v : MatrixView α m n) : Q(Matrix $m $n $α) :=
  match v with
  | .literal _zα k l _ _ A => q(ofLists $k $l $(A.lit))
  | .functional f => q(Matrix.of $f)

/-- A view that builds the matrix term `M`. -/
structure MatrixViewOf {u : Level} {α : Q(Type u)} {m n : Q(Type)} (M : Q(Matrix $m $n $α)) where
  /-- A view of `M`. -/
  view : MatrixView α m n
  /-- The proof that `view` builds `M`. -/
  proof : Q($M = $(view.toMatrix))

/-- A view that builds the term `M`: the literal view when `M` is a `!![…]` literal, and the
functional view of `M` otherwise. -/
def MatrixViewOf.parse {u : Level} {α : Q(Type u)} {m n : Q(Type)} (zα : Q(Zero $α))
    (M : Q(Matrix $m $n $α)) : MetaM (MatrixViewOf M) := do
  let some (k, l, _, entries) ← matchMatrixLit? M (closed := false)
    | let f : Q($m → $n → $α) := M
      return ⟨.functional f, q(rfl)⟩
  -- `matchMatrixLit?` read `k` and `l` off the type `Matrix (Fin k) (Fin l) α` of `M`.
  have hm : $m =Q Fin $k := ⟨⟩
  have hn : $n =Q Fin $l := ⟨⟩
  let A := ListMatrixLit.ofArray k l entries
  have : $M =Q ofLists $k $l $(A.lit) := ⟨⟩
  return ⟨.literal zα k l hm hn A, q(rfl)⟩

end Mathlib.Tactic.Matrix
