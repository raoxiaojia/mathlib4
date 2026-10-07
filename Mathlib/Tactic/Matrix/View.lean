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

`MatrixView` records how a tactic reads a matrix term `M`. A `!![…]` literal is read through the
lists of its rows, and any other term entry by entry.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

/-- Three forms of one list-based matrix literal. This makes the argument list more succinct when
a cert construction function needs to use multiple representations. -/
structure ListMatrixLit (u : Level) (m n : Nat) (α : Q(Type u)) where
  /-- The matrix, the `ofLists` term on `lit`. -/
  matrix : Q(Matrix (Fin $m) (Fin $n) $α)
  /-- The list literal of `rows`. -/
  lit : Q(List (List $α))
  /-- The rows of the matrix. -/
  rows : List (List Q($α))

/-- The `ListMatrixLit` of the matrix with rows `rows`. -/
def ListMatrixLit.ofArray {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (rows : Array (Array Q($α))) : ListMatrixLit u m n α :=
  let rows := rows.toList.map Array.toList
  let lit : Q(List (List $α)) := mkListLitQ (α := q(List $α)) (rows.map mkListLitQ)
  { matrix := q(ofLists $m $n $lit), lit, rows }

/-- How a tactic reads the matrix term `M`. -/
inductive MatrixView {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (M : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- `M` is a `!![…]` literal, equal to the list-based literal `l`. -/
  | literal (l : ListMatrixLit u m n α) (pf : Q($M = ofLists $m $n $(l.lit)))
  /-- `M` is the matrix of the function `f`, read entry by entry. -/
  | functional (f : Q(Fin $m → Fin $n → $α)) (pf : Q($M = Matrix.of $f))

/-- The view of `M` (`literal` for a closed `!![…]` literal and `functional` otherwise). -/
def MatrixView.parse {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (m n : Nat)
    (M : Q(Matrix (Fin $m) (Fin $n) $α)) : MetaM (MatrixView zα m n M) := do
  let some (_, _, _, entries) ← matchMatrixLit? M
    | let f : Q(Fin $m → Fin $n → $α) := M
      return .functional f q(rfl)
  let l := ListMatrixLit.ofArray zα m n entries
  have : $M =Q ofLists $m $n $(l.lit) := ⟨⟩
  return .literal l q(rfl)

end Mathlib.Tactic.Matrix
