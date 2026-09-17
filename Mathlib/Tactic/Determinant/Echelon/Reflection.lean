/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Reflection certificates for determinants of echelon decompositions

The diagonal product of a matrix given as a list of rows, with a bridge lemma to the product over
`Fin m` of an `ofLists` matrix, and the sign of a permutation given as a chain of swaps.

## Main definitions

- `diagProd`

## Main results

- `prod_diag_ofLists`
- `intCast_sign_swap_trans`
-/

@[expose] public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Determinant

variable {α : Type*}

/-! ### Diagonal products -/

/-- The product of the `c` entries at columns `k, k + 1, …` of successive rows, a missing row
contributing `0`. -/
def diagProd [Zero α] [One α] [Mul α] (k : ℕ) : ℕ → List (List α) → α
  | 0, _ => 1
  | _ + 1, [] => 0
  | c + 1, row :: rows => row.getD k 0 * diagProd (k + 1) c rows

theorem diagProd_zero [Zero α] [One α] [Mul α] (k : ℕ) (rows : List (List α)) :
    diagProd k 0 rows = 1 :=
  rfl

theorem diagProd_succ_cons [Zero α] [One α] [Mul α] {k c : ℕ} {row : List α}
    {rows : List (List α)} {a e : α} (hd : row.getD k 0 = a) (h : diagProd (k + 1) c rows = e) :
    diagProd k (c + 1) (row :: rows) = a * e := by
  rw [diagProd, hd, h]

theorem prod_getD_eq_diagProd [CommMonoidWithZero α] (k c : ℕ) (rows : List (List α)) :
    ∏ i : Fin c, (rows.getD i []).getD (k + i) 0 = diagProd k c rows := by
  induction c generalizing k rows with
  | zero => simp [diagProd]
  | succ c ih =>
    cases rows <;>
      simp [diagProd, Fin.prod_univ_succ, ← ih, Nat.add_right_comm _ _ 1, ← Nat.add_assoc]

theorem prod_diag_ofLists [CommMonoidWithZero α] (m : ℕ) (rows : List (List α)) :
    ∏ i, ofLists m m rows i i = diagProd 0 m rows := by
  simpa using prod_getD_eq_diagProd 0 m rows

/-! ### Signs of chains of swaps -/

variable {n : Type*} [DecidableEq n] [Fintype n] {σ : Equiv.Perm n} {x y : n}

theorem intCast_sign_refl [Ring α] : ((Equiv.Perm.sign (Equiv.refl n) : ℤ) : α) = 1 := by
  simp

theorem intCast_sign_swap_trans [Ring α] {s : α} (h : ((Equiv.Perm.sign σ : ℤ) : α) = s)
    (hxy : x ≠ y) : ((Equiv.Perm.sign ((Equiv.swap x y).trans σ) : ℤ) : α) = -s := by
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hxy, ← h]
  simp

end Mathlib.Tactic.Determinant
