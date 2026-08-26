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
- `Echelon.Decomposition.map`: transport of a certificate along an injective ring
  homomorphism.
- `Echelon.Decomposition.congr`: transport of a certificate along a matrix equality.

## Main results

- `Echelon.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.

## Tags

matrix, echelon form
-/

public section

variable
  {m : Type*} [Fintype m] [LinearOrder m]
  {n : Type*} [Fintype n] [LinearOrder n]
  {R : Type*} [CommRing R]

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

/-- Transport a certificate along an equality of matrices, keeping its data. -/
@[expose] def Decomposition.congr {A B : Matrix m n R} (cert : Decomposition A)
    (h : A = B) : Decomposition B where
  L := cert.L
  σ := cert.σ
  pivot := cert.pivot
  isPivotedBy := h ▸ cert.isPivotedBy
  L_lowerTriangular := cert.L_lowerTriangular
  L_diag_ne_zero := cert.L_diag_ne_zero

theorem Decomposition.rank_eq [IsDomain R] {A : Matrix m n R} (cert : Decomposition A) :
    A.rank = #{i | cert.pivot i ≠ ⊤} := by
  rw [← cert.isPivotedBy.rank_eq,
    cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

variable {S : Type*} [CommRing S]

/-- An echelon decomposition certificate transports along an injective ring
homomorphism. -/
@[expose] def Decomposition.map {A : Matrix m n R} (cert : Decomposition A) (f : R →+* S)
    (hf : Function.Injective f) : Decomposition (A.map f) where
  L := cert.L.map f
  σ := cert.σ
  pivot := cert.pivot
  isPivotedBy := by
    rw [Matrix.submatrix_map, ← Matrix.map_mul]
    exact cert.isPivotedBy.map f hf
  L_lowerTriangular := cert.L_lowerTriangular.map f
  L_diag_ne_zero i := (map_ne_zero_iff f hf).mpr (cert.L_diag_ne_zero i)

end Echelon
