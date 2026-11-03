/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithm enclosures for interval_dyadic_real

This file defines an inclusion operation for the `interval_dyadic_real` inclusion family that
encloses `Real.log` of an interval.
-/

public section

open Finset

namespace Inclusion

namespace IntervalDyadicReal

/-- The factor `N` of the numerator and the factor `P` of the denominator in
`∑ i ∈ range n, (a / b) ^ (2 * i + 1) / (2 * i + 1) = a * N / (b ^ (2 * n + 1) * P)`. -/
@[expose]
def artanhPartialSumNumDenom (a b n : ℕ) : ℕ × ℕ :=
  match n with
  | 0 => (0, 1)
  | n + 1 =>
    let p := artanhPartialSumNumDenom a b n
    ((p.1 * (2 * n + 1) + a ^ (2 * n) * p.2) * b ^ 2, p.2 * (2 * n + 1))

theorem artanhPartialSumNumDenom_snd_pos (a b n : ℕ) :
    0 < (artanhPartialSumNumDenom a b n).2 := by
  induction n <;> simp [artanhPartialSumNumDenom, *]

theorem artanhPartialSumNumDenom_div (a : ℤ) {b : ℕ} (hb : b ≠ 0) (n : ℕ) :
    (a : ℝ) * (artanhPartialSumNumDenom a.natAbs b n).1 /
        (b ^ (2 * n + 1) * (artanhPartialSumNumDenom a.natAbs b n).2) =
      ∑ i ∈ range n, ((a : ℝ) / b) ^ (2 * i + 1) / (2 * i + 1) := by
  induction n with
  | zero => simp [artanhPartialSumNumDenom]
  | succ n ih =>
    have hP := (artanhPartialSumNumDenom_snd_pos a.natAbs b n).ne'
    rw [sum_range_succ, ← ih, artanhPartialSumNumDenom]
    push_cast [Nat.cast_natAbs, pow_mul, sq_abs, div_pow]
    field_simp
    ring

/-- The remainder bound of `Real.sum_range_sub_log_div_le` for the first `n` terms of
`log (a / b) = 2 ∑ i, z ^ (2 * i + 1) / (2 * i + 1)` with `z = (a - b) / (a + b)`. -/
theorem abs_log_div_sub_le_of_artanhPartialSumNumDenom_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) {p : ℕ × ℕ}
    (hp : artanhPartialSumNumDenom (a - b : ℤ).natAbs (a + b) n = p) :
    |Real.log (a / b) - 2 * ((a - b : ℤ) : ℝ) * p.1 / ((a + b : ℕ) ^ (2 * n + 1) * p.2)| ≤
      |((a - b : ℤ) : ℝ)| ^ (2 * n + 1) * (a + b : ℕ) ^ 2 /
        (2 * a * b * (a + b : ℕ) ^ (2 * n + 1)) := by
  have ha₀ : (0 : ℝ) < a := by exact_mod_cast ha
  have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
  set x : ℝ := ((a - b : ℤ) : ℝ) / (a + b : ℕ) with hx
  have hx1 : |x| < 1 := by
    rw [hx, abs_div, Nat.abs_cast, div_lt_one (by positivity), abs_lt]
    push_cast
    constructor <;> linarith
  have h1 : (1 + x) / (1 - x) = a / b := by
    rw [div_eq_div_iff (sub_pos.mpr (abs_lt.mp hx1).2).ne' hb₀.ne', hx]
    push_cast
    field_simp
    ring
  have h2 : 1 - x ^ 2 = 4 * a * b / (a + b) ^ 2 := by
    rw [hx]
    push_cast
    field_simp
    ring
  have key := Real.sum_range_sub_log_div_le hx1 n
  rw [hx, ← artanhPartialSumNumDenom_div _ (by positivity), ← hx, h1, h2, hp] at key
  calc _ = 2 * |1 / 2 * Real.log (a / b) -
        ((a - b : ℤ) : ℝ) * p.1 / ((a + b : ℕ) ^ (2 * n + 1) * p.2)| := by
        rw [← abs_two, ← abs_mul]
        congr 1
        ring
    _ ≤ 2 * (|x| ^ (2 * n + 1) / (4 * a * b / (a + b) ^ 2)) := by gcongr
    _ = _ := by
        rw [hx, abs_div, Nat.abs_cast, div_pow]
        push_cast
        field_simp
        ring

/-- An enclosure of `log (a / b) + e * log 2` by `n₁` terms of the series of
`abs_log_div_sub_le_of_artanhPartialSumNumDenom_eq` for `log (a / b)` and `n₂` terms of that for
`log 2 = log (2 / 1)`, summed over a common denominator and rounded outward to precision `prec`. -/
@[expose]
def logRatSeries (a b : ℕ) (e : ℤ) (n₁ n₂ prec : ℕ) : Interval Dyadic :=
  let s : ℤ := a - b
  let t := a + b
  let p := artanhPartialSumNumDenom s.natAbs t n₁
  let q := artanhPartialSumNumDenom 1 3 n₂
  let d₁ := t ^ (2 * n₁ + 1) * p.2
  let d₂ := 3 ^ (2 * n₂ + 1) * q.2
  ratBall (8 * a * b * (s * p.1 * d₂ + e * q.1 * d₁))
    (2 * s.natAbs ^ (2 * n₁ + 1) * t ^ 2 * p.2 * d₂ + 9 * a * b * e.natAbs * q.2 * d₁ : ℕ)
    (4 * a * b * d₁ * d₂) prec

theorem logRatSeries_mem {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (e : ℤ) (n₁ n₂ prec : ℕ) :
    Real.log (a / b) + e * Real.log 2 ∈ logRatSeries a b e n₁ n₂ prec := by
  have h₁ := abs_log_div_sub_le_of_artanhPartialSumNumDenom_eq ha hb n₁ rfl
  have h₂ := abs_log_div_sub_le_of_artanhPartialSumNumDenom_eq (a := 2) (b := 1) (by norm_num)
    (by norm_num) n₂ (p := artanhPartialSumNumDenom 1 3 n₂) rfl
  have hP := artanhPartialSumNumDenom_snd_pos (a - b : ℤ).natAbs (a + b) n₁
  have hQ := artanhPartialSumNumDenom_snd_pos 1 3 n₂
  refine ratBall_mem ?_ prec
  norm_num at h₂
  push_cast at h₁ ⊢
  have h₃ := mul_le_mul_of_nonneg_left h₂ (abs_nonneg (e : ℝ))
  rw [← abs_mul] at h₃
  convert (abs_add_le _ _).trans (add_le_add h₁ h₃) using 2 <;>
  · field_simp
    ring

/-- An enclosure of `log x` within about `2 ^ (-prec)`, by `logRatSeries` after writing `|x|` as
`2 ^ e * y` with `y ∈ [1 / √2, √2)`. -/
@[expose]
def logPoint (x : Dyadic) (prec : ℕ) : Interval Dyadic :=
  match x with
  | .zero => Interval.singleton 0
  | .ofOdd n k _ =>
    let u := n.natAbs
    -- `y = u / 2 ^ j ∈ [1 / √2, √2)` and `x = ± 2 ^ e * y`.
    let j := if 2 * 4 ^ u.log2 ≤ u ^ 2 then u.log2 + 1 else u.log2
    let e : ℤ := j - k
    let s : ℤ := u - 2 ^ j
    -- Each series stops once its remainder bound is below `2 ^ (-prec - 3)`, and is skipped when
    -- it does not contribute. The series of `y` has `z = s / (u + 2 ^ j)`, and each of its terms
    -- gains `max 5 (2 m)` bits for `m = ⌊log₂ ⌊(u + 2 ^ j) / |s|⌋⌋`, since `|z| ≤ 2 ^ (-m)` and
    -- `|z| ≤ 3 - 2√2 < 2 ^ (-5 / 2)`. The series of `log 2` has `z = 1 / 3` and its remainder bound
    -- is `(3 / 4) 9 ^ (-n₂)`, scaled by `|e|`.
    let n₁ := if s = 0 then 0 else (prec + 3) / max 5 (2 * ((u + 2 ^ j) / s.natAbs).log2) + 1
    let n₂ := if e = 0 then 0 else (prec + e.natAbs.log2 + 4) / 3 + 1
    logRatSeries u (2 ^ j) e n₁ n₂ prec

theorem logPoint_mem (x : Dyadic) (prec : ℕ) : Real.log x.toReal ∈ logPoint x prec := by
  cases x with
  | zero =>
    simpa [logPoint, mem_iff_mem_map, Dyadic.toReal] using
      Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
  | ofOdd n k hn =>
    have hn0 : n ≠ 0 := by lia
    have key (j : ℕ) : Real.log (Dyadic.ofOdd n k hn).toReal =
        Real.log ((n.natAbs : ℝ) / (2 ^ j : ℕ)) + ((j - k : ℤ) : ℝ) * Real.log 2 := by
      rw [Dyadic.toReal, Dyadic.toRat_ofOdd_eq_mul_two_pow]
      push_cast
      rw [Real.log_mul (by exact_mod_cast hn0) (by positivity), Real.log_zpow,
        Real.log_div (by positivity) (by positivity), Real.log_pow, Nat.cast_natAbs, Int.cast_abs,
        Real.log_abs]
      push_cast
      ring
    dsimp only [logPoint]
    rw [key]
    exact logRatSeries_mem (Int.natAbs_pos.mpr hn0) (by positivity) _ _ _ prec

/-- The logarithm of an interval, from `log x = log |x|` and the enclosures `logPoint` at the
endpoints of `|I|`. When `|I|` contains `0`, the result is unbounded below, except that `|I| = {0}`
gives `{0}`. A finite upper endpoint `u` of `|I|` then gives the upper endpoint of
`logPoint (max 1 u)`, since `log 0 = 0 = log 1`. -/
@[expose]
def log (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.abs with
  | ⟨some l, ub⟩ =>
    if 0 < l then
      { lb := (logPoint l prec).lb
        ub := match ub with
          | some u => (logPoint u prec).ub
          | ⊤ => ⊤ }
    else
      match ub with
      | some u => if u = 0 then Interval.singleton 0 else Interval.Iic (logPoint (max 1 u) prec).ub
      | ⊤ => Interval.univ Dyadic
  | ⟨⊥, _⟩ => Interval.univ Dyadic

@[inclusion_op interval_dyadic_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.log x ∈ log I prec := by
  have hy₀ : 0 ≤ |x| := abs_nonneg x
  have hy := abs_mem hx
  rw [← Real.log_abs]
  dsimp only [log]
  generalize |x| = y at hy₀ hy
  generalize I.abs = J at hy
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hy
  rw [mem_iff_mem_map]
  rcases J with ⟨_ | l, ub⟩
  · exact Interval.mem_map_univ _ _
  dsimp only
  split_ifs with hl
  · have hl₀ : 0 < l.toReal := by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr hl
    have hly := Real.log_le_log hl₀ (hy.1 l rfl)
    rcases ub with _ | u
    · exact Interval.mem_Ici_of_le hly (logPoint_mem l prec)
    · exact Interval.mem_Icc_of_le (logPoint_mem l prec) hly
        (Real.log_le_log (hl₀.trans_le (hy.1 l rfl)) (hy.2 u rfl)) (logPoint_mem u prec)
  rcases ub with _ | u
  · exact Interval.mem_map_univ _ _
  dsimp only
  split_ifs with hu
  · have : y = 0 := le_antisymm (by simpa [hu, Dyadic.toReal] using hy.2 u rfl) hy₀
    simpa [this, Dyadic.toReal] using Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
  · refine Interval.mem_Iic_of_le ?_ (logPoint_mem (max 1 u) prec)
    have h₁ : (1 : Dyadic).toReal = 1 := by exact_mod_cast Dyadic.toReal_natCast 1
    rw [Monotone.map_max (f := Dyadic.toReal) Dyadic.toRealOrderEmbedding.monotone, h₁]
    rcases hy₀.eq_or_lt with rfl | hy₀
    · simpa using Real.log_nonneg (le_max_left _ _)
    · exact Real.log_le_log hy₀ ((hy.2 u rfl).trans (le_max_right _ _))

end IntervalDyadicReal

end Inclusion
