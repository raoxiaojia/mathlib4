/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Echelon decomposition certificates

`Echelon.Decomposition A` certifies an echelon decomposition of the matrix `A`.

## Main definitions

- `Echelon.Decomposition`: the certificate structure.

## Main results

- `Echelon.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.
- `Echelon.Decomposition.det_eq`: `A.det` from the diagonal products of a certificate for `A`.

## Tags

matrix, echelon form
-/

public section

variable
  {m : Type*} [Fintype m] [LinearOrder m]
  {n : Type*} [Fintype n] [LinearOrder n]
  {R : Type*} [CommRing R] [IsDomain R]

namespace Echelon

open scoped Finset

/-- A certificate of an echelon form decomposition of `A`, certifying that
`L * (A.submatrix σ id)` is in echelon form by providing a pivot, where `L`
is lower triangular with nonzero diagonal, and `σ` the permutation on the rows
of `A`.
This version does not store the final echelon form itself as it can be computed
by the data enclosed.
-/
structure Decomposition (A : Matrix m n R) where
  /-- The transformation matrix. -/
  L : Matrix m m R
  /-- The row permutation on the rows of `A`. -/
  σ : Equiv.Perm m
  /-- The pivot of the resulting echelon form. -/
  pivot : m → WithTop n
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : m) : L.diag i ≠ 0

theorem Decomposition.rank_eq {A : Matrix m n R} (cert : Decomposition A) :
    A.rank = #{i | cert.pivot i ≠ ⊤} := by
  rw [← cert.isPivotedBy.rank_eq,
    cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

theorem Decomposition.det_eq {A : Matrix m m R} (cert : Decomposition A) {U : Matrix m m R}
    {l u s v : R} (hU : cert.L * A.submatrix cert.σ id = U) (hl : ∏ i, cert.L i i = l)
    (hu : ∏ i, U i i = u) (hs : ((Equiv.Perm.sign cert.σ : ℤ) : R) = s) (hv : l * (s * v) = u) :
    A.det = v := by
  have hl0 : l ≠ 0 := hl ▸ Finset.prod_ne_zero_iff.mpr fun i _ => cert.L_diag_ne_zero i
  have hs0 : s ≠ 0 := by
    rw [← hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign cert.σ) with h | h <;> simp [h]
  refine mul_left_cancel₀ hs0 (mul_left_cancel₀ hl0 (Eq.trans ?_ hv.symm))
  rw [← hu, ← (hU ▸ cert.isPivotedBy : U.IsPivotedBy cert.pivot).det_eq, ← hU, Matrix.det_mul,
    Matrix.det_permute, ← hs, ← hl, ← Matrix.det_of_isLowerTriangular _ cert.L_lowerTriangular]

end Echelon
