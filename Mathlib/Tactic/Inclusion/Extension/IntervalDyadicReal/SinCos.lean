/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Sine and cosine enclosures for interval_dyadic_real

This file defines inclusion operations for the `interval_dyadic_real` inclusion family that
enclose `Real.sin` and `Real.cos` of an interval.

## Implementation notes

The sine of a point `x` is computed by enclosing `sin (x / 3 ^ k)` with a Taylor partial sum and
then applying the triple-angle formula `sin (3 * y) = 3 * sin y - 4 * sin y ^ 3` to it `k` times.
Periodicity is not used yet.

This file is opt-in so that `dyadic_interval` doesn't import unnecessary theories.
-/

public section

open Finset

open scoped Nat

namespace Inclusion

namespace IntervalDyadicReal
open Inclusion.IntervalDyadicReal

/-! ### Enclosures at a point -/

/-- The numerator of the partial Taylor sum
`∑ m ∈ range n, (-1) ^ m * (a / b) ^ (2 * m + 1) / (2 * m + 1)!` as an unreduced fraction over the
common denominator `b ^ (2 * n + 1) * (2 * n + 1)!`. -/
@[expose]
def sinPartialSumNum (a : ℤ) (b n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | n + 1 =>
    (sinPartialSumNum a b n + (-1) ^ n * a ^ (2 * n + 1)) *
      (b ^ 2 * ((2 * n + 2) * (2 * n + 3)) : ℕ)

theorem sinPartialSumNum_div (a : ℤ) {b : ℕ} (hb : b ≠ 0) (n : ℕ) :
    (sinPartialSumNum a b n : ℝ) / (b ^ (2 * n + 1) * (2 * n + 1)!) =
      ∑ m ∈ range n, (-1) ^ m * ((a : ℝ) / b) ^ (2 * m + 1) / (2 * m + 1)! := by
  induction n with
  | zero => simp [sinPartialSumNum]
  | succ n ih =>
    rw [sum_range_succ, ← ih, sinPartialSumNum, mul_add_one, Nat.factorial_succ, Nat.factorial_succ]
    push_cast [div_pow]
    field_simp
    ring

/-- An enclosure of `sin (a / b)` by the first `n` terms of its Taylor series and the remainder
bound of `Real.abs_sin_sub_sum_range_le`, rounded outward to precision `prec`. This is only
intended for use when `|a / b| ≤ 1`. -/
@[expose]
def sinRatTaylor (a : ℤ) (b n prec : ℕ) : Interval Dyadic :=
  ratBall (sinPartialSumNum a b n) (|a| ^ (2 * n + 1)) (b ^ (2 * n + 1) * (2 * n + 1)!) prec

theorem sinRatTaylor_mem (a : ℤ) {b : ℕ} (hb : b ≠ 0) (hab : a.natAbs ≤ b) (n prec : ℕ) :
    Real.sin (a / b) ∈ sinRatTaylor a b n prec := by
  have hy : |(a : ℝ) / b| ≤ 1 := by
    rw [abs_div, Nat.abs_cast, div_le_one (by positivity), ← Int.cast_abs, ← Int.natCast_natAbs]
    norm_cast
  refine ratBall_mem ?_ prec
  push_cast
  rw [sinPartialSumNum_div a hb n]
  refine (Real.abs_sin_sub_sum_range_le hy n).trans_eq ?_
  rw [abs_div, Nat.abs_cast, div_pow, div_div]

/-- Apply the triple-angle formula `sin (3 * y) = 3 * sin y - 4 * sin y ^ 3` `k` times to an
enclosure `I` of `sin y`, rounding outward to precision `prec` after each step. -/
@[expose]
def sinTripleAngle (k : ℕ) (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match k with
  | 0 => I
  | k + 1 =>
    sinTripleAngle k
      (roundOut (((Interval.singleton 3).mul I).sub ((Interval.singleton 4).mul (I.pow 3))) prec)
      prec

theorem sinTripleAngle_mem {y : ℝ} {I : Interval Dyadic} (hy : Real.sin y ∈ I) (k prec : ℕ) :
    Real.sin (3 ^ k * y) ∈ sinTripleAngle k I prec := by
  induction k generalizing y I with
  | zero => simpa [sinTripleAngle] using hy
  | succ k ih =>
    rw [sinTripleAngle, pow_succ, mul_assoc]
    refine ih ?_
    rw [Real.sin_three_mul]
    exact roundOut_mem
      (sub_mem (mul_mem (ofNat_mem 3) hy) (mul_mem (ofNat_mem 4) (pow_mem 3 hy))) prec

/-- An enclosure of `sin x`, computed from `sin (x / 3 ^ k)` by `sinTripleAngle`.

Some relevant precision constants are chosen as follows:
- `k = ⌊log₂ (⌊|x|⌋ + 1)⌋ + 3 + e`, so that `|x / 3 ^ k| < 2 ^ (-3 - e)`. The number `e` of
  extra steps grows as `√prec` to balance the cost of the triple-angle steps against that of the
  Taylor terms. With `e = 0`, about `prec / 8` terms are needed, and from about `16000` bits their
  recursion exceeds the default `maxRecDepth`.
- `precTaylor` adds `4` bits per triple-angle step to `prec` (a step widens an interval by a factor
  of at most `15`) and `8` more bits so that the result has width at most `2 ^ (-prec)`.
- `taylorTerms` terms bring the remainder below `2 ^ (-precTaylor)`, since each term shrinks it by
  at least `2 * e + 6` bits from the bound on `|x / 3 ^ k|` and `2` bits from the factorial.
-/
@[expose]
def sinPoint (x : Dyadic) (prec : ℕ) : Interval Dyadic :=
  let r := x.toRat
  let e := Nat.sqrt prec / 4
  let k := Nat.log2 (r.num.natAbs / r.den + 1) + 3 + e
  let precTaylor := prec + 4 * k + 8
  let taylorTerms := precTaylor / (2 * e + 8) + 1
  roundOut (sinTripleAngle k (sinRatTaylor r.num (r.den * 3 ^ k) taylorTerms precTaylor)
    precTaylor) (prec + 1)

theorem sinPoint_mem (x : Dyadic) (prec : ℕ) : Real.sin x.toReal ∈ sinPoint x prec := by
  dsimp only [sinPoint]
  generalize hk : Nat.log2 (x.toRat.num.natAbs / x.toRat.den + 1) + 3 + Nat.sqrt prec / 4 = k
  have hred : x.toReal = 3 ^ k * (x.toRat.num / (x.toRat.den * 3 ^ k : ℕ)) := by
    rw [Dyadic.toReal, Rat.cast_def]
    push_cast
    field_simp
  have hab : x.toRat.num.natAbs ≤ x.toRat.den * 3 ^ k := by
    have h : x.toRat.num.natAbs / x.toRat.den + 1 ≤ 3 ^ k :=
      (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by lia) (by lia))).trans
        (Nat.pow_le_pow_left (by lia) k)
    exact (Nat.lt_mul_div_succ _ x.toRat.den_pos).le.trans (Nat.mul_le_mul_left _ h)
  rw [hred]
  exact roundOut_mem (sinTripleAngle_mem (sinRatTaylor_mem _ (by positivity) hab _ _) k _) _

/-- An enclosure of `cos x`, computed from `sinPoint (x / 2)` by
`cos x = 1 - 2 * sin (x / 2) ^ 2`. `sinPoint` gets `2` extra bits since `1 - 2 * s ^ 2` multiplies
an error in `s` by at most `4`. -/
@[expose]
def cosPoint (x : Dyadic) (prec : ℕ) : Interval Dyadic :=
  (Interval.singleton 1).sub
    ((Interval.singleton 2).mul ((sinPoint (x >>> (1 : ℕ)) (prec + 2)).pow 2))

theorem cosPoint_mem (x : Dyadic) (prec : ℕ) : Real.cos x.toReal ∈ cosPoint x prec := by
  have h1 : (1 : ℝ) ∈ Interval.singleton (1 : Dyadic) := by simpa using natCast_mem 1
  have hx : x.toReal = 2 * (x >>> (1 : ℕ)).toReal := by
    simp only [Dyadic.toReal, Dyadic.toRat_shiftRight_nat]
    push_cast
    ring
  rw [hx, Real.cos_two_mul_eq_one_sub]
  exact sub_mem h1 (mul_mem (ofNat_mem 2) (pow_mem 2 (sinPoint_mem _ _)))

/-! ### Enclosures on an interval

An interval narrower than `π` contains at most one extremum of `sin`. It is enclosed from `sin`
and `cos` at its endpoints. A bound is replaced by `±1` unless their signs rule out an extremum
inside.
-/

theorem sin_le_max_of_cos_nonpos_or_cos_nonneg_or_sin_neg {l u x : ℝ} (hlx : l ≤ x)
    (hxu : x ≤ u) (hw : u - l < Real.pi)
    (h : (Real.cos l ≤ 0 ∨ 0 ≤ Real.cos u) ∨ (Real.sin l < 0 ∧ Real.sin u < 0)) :
    Real.sin x ≤ max (Real.sin l) (Real.sin u) := by
  by_contra! hlt
  obtain ⟨c, ⟨hlc, hcu⟩, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨x, hlx, hxu⟩ Real.continuous_sin.continuousOn
  have hxc : Real.sin x ≤ Real.sin c := hmax ⟨hlx, hxu⟩
  replace hlc : l < c := by grind
  replace hcu : c < u := by grind
  have hcos : Real.cos c = 0 :=
    (hmax.isLocalMax (Icc_mem_nhds hlc hcu)).hasDerivAt_eq_zero (Real.hasDerivAt_sin c)
  have hsin : Real.sin c = 1 := by grind [Real.cos_eq_zero_iff_sin_eq, Real.neg_one_le_sin]
  have h1 : 0 < Real.cos l := by
    simpa [Real.sin_sub, hsin, hcos] using Real.sin_pos_of_pos_of_lt_pi (x := c - l)
      (by linarith) (by linarith)
  have h2 : Real.cos u < 0 := by
    simpa [Real.sin_sub, hsin, hcos] using Real.sin_pos_of_pos_of_lt_pi (x := u - c)
      (by linarith) (by linarith)
  have h3 : 0 < Real.sin l ∨ 0 < Real.sin u := by
    by_cases ht : c - l < Real.pi / 2
    · left
      simpa [Real.cos_sub, hsin, hcos] using
        Real.cos_pos_of_mem_Ioo (x := c - l) ⟨by linarith [Real.pi_pos], ht⟩
    · right
      simpa [Real.cos_sub, hsin, hcos] using
        Real.cos_pos_of_mem_Ioo (x := u - c) ⟨by linarith [Real.pi_pos], by linarith⟩
  grind

theorem min_le_sin_of_cos_nonneg_or_cos_nonpos_or_sin_pos {l u x : ℝ} (hlx : l ≤ x)
    (hxu : x ≤ u) (hw : u - l < Real.pi)
    (h : (0 ≤ Real.cos l ∨ Real.cos u ≤ 0) ∨ (0 < Real.sin l ∧ 0 < Real.sin u)) :
    min (Real.sin l) (Real.sin u) ≤ Real.sin x := by
  have := sin_le_max_of_cos_nonpos_or_cos_nonneg_or_sin_neg (l := -u) (u := -l) (neg_le_neg hxu)
    (neg_le_neg hlx) (by linarith) <| by
      rw [Real.cos_neg, Real.cos_neg, Real.sin_neg, Real.sin_neg, neg_lt_zero, neg_lt_zero]
      rcases h with (h | h) | ⟨h1, h2⟩
      exacts [Or.inl (Or.inr h), Or.inl (Or.inl h), Or.inr ⟨h2, h1⟩]
  simpa [Real.sin_neg, max_neg_neg, min_comm] using this

/-- An enclosure of `Real.sin` on `[l, u]` for `u - l < π`. A bound is left open when an extremum
may lie inside (`sin` clips it to `±1`). -/
@[expose]
def sinIcc (l u : Dyadic) (prec : ℕ) : Interval Dyadic :=
  let sl := sinPoint l prec
  let su := sinPoint u prec
  let cl := cosPoint l prec
  let cu := cosPoint u prec
  let z := Interval.singleton (0 : Dyadic)
  let H := sl.hull su
  ⟨if (((z.le cl).or (cu.le z)).or ((z.lt sl).and (z.lt su))).isTrue then H.lb else ⊥,
    if (((cl.le z).or (z.le cu)).or ((sl.lt z).and (su.lt z))).isTrue then H.ub else ⊤⟩

theorem sinIcc_mem {l u : Dyadic} {x : ℝ} (hlx : l.toReal ≤ x) (hxu : x ≤ u.toReal)
    (hw : u.toReal - l.toReal < Real.pi) (prec : ℕ) : Real.sin x ∈ sinIcc l u prec := by
  have hsl := sinPoint_mem l prec
  have hsu := sinPoint_mem u prec
  have hcl := cosPoint_mem l prec
  have hcu := cosPoint_mem u prec
  have hz : (0 : ℝ) ∈ Interval.singleton (0 : Dyadic) := by simpa using natCast_mem 0
  have hHl : Real.sin l.toReal ∈ (sinPoint l prec).hull (sinPoint u prec) :=
    Interval.hull_mem_left Dyadic.toRealOrderEmbedding hsl
  have hHu : Real.sin u.toReal ∈ (sinPoint l prec).hull (sinPoint u prec) :=
    Interval.hull_mem_right Dyadic.toRealOrderEmbedding hsu
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hHl hHu ⊢
  constructor
  · intro a ha
    simp only [sinIcc] at ha
    split_ifs at ha with h
    · have hc := true_of_mem_intervalBool_eq_true
        (IntervalBool.or_mem (IntervalBool.or_mem (le_mem hz hcl) (le_mem hcu hz))
          (IntervalBool.and_mem (lt_mem hz hsl) (lt_mem hz hsu)))
        (IntervalBool.eq_true_of_isTrue_eq_true h)
      have hmin := min_le_sin_of_cos_nonneg_or_cos_nonpos_or_sin_pos hlx hxu hw hc
      exact (le_min (hHl.1 a ha) (hHu.1 a ha)).trans hmin
    · exact absurd ha WithBot.bot_ne_coe
  · intro a ha
    simp only [sinIcc] at ha
    split_ifs at ha with h
    · have hc := true_of_mem_intervalBool_eq_true
        (IntervalBool.or_mem (IntervalBool.or_mem (le_mem hcl hz) (le_mem hz hcu))
          (IntervalBool.and_mem (lt_mem hsl hz) (lt_mem hsu hz)))
        (IntervalBool.eq_true_of_isTrue_eq_true h)
      have hmax := sin_le_max_of_cos_nonpos_or_cos_nonneg_or_sin_neg hlx hxu hw hc
      exact hmax.trans (max_le (hHl.2 a ha) (hHu.2 a ha))
    · exact absurd ha WithTop.top_ne_coe

/-- An enclosure of `Real.sin` on `I` by `sinPoint` for a point and by `sinIcc` for a bounded
interval of width at most `3 < π` (`Interval.univ` otherwise). -/
@[expose]
def sinNarrow (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I with
  | ⟨some l, some u⟩ =>
    if l = u then sinPoint l prec else if u ≤ l + 3 then sinIcc l u prec else Interval.univ Dyadic
  | _ => Interval.univ Dyadic

theorem sinNarrow_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sin x ∈ sinNarrow I prec := by
  match I with
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ => exact Interval.mem_map_univ _ _
  | ⟨some l, some u⟩ =>
    rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
    have hlx : l.toReal ≤ x := hx.1 l rfl
    have hxu : x ≤ u.toReal := hx.2 u rfl
    simp only [sinNarrow]
    split_ifs with he h3
    · subst he
      exact le_antisymm hxu hlx ▸ sinPoint_mem l prec
    · have h3 : u.toReal ≤ l.toReal + 3 := by simpa using Dyadic.toReal_le_toReal.mpr h3
      exact sinIcc_mem hlx hxu (by linarith [Real.pi_gt_three]) prec
    · exact Interval.mem_map_univ _ _

/-- The sine of an interval, clipped to `[-1, 1]`. A bounded interval of width less than `7` is
bisected until its pieces have width at most `3`, each enclosed by `sinNarrow`. Any other interval
is enclosed by `[-1, 1]`, which is exact since it is wider than `2 * π`. -/
@[expose]
def sin (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let depth := match I with
    | ⟨some l, some u⟩ =>
      if u ≤ l + 3 then 0 else if u ≤ l + 6 then 1 else if u < l + 7 then 2 else 0
    | _ => 0
  (binarySplitMap depth I (sinNarrow · prec)).inter (Interval.Icc (-1 : Dyadic) (1 : Dyadic))

@[inclusion_op interval_dyadic_real]
theorem sin_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sin x ∈ sin I prec := by
  have hC : Real.sin x ∈ Interval.Icc (α := Dyadic) (-1 : Dyadic) (1 : Dyadic) :=
    Interval.mem_map_Icc _ (by simpa [Dyadic.toReal] using Real.neg_one_le_sin x)
      (by simpa [Dyadic.toReal] using Real.sin_le_one x)
  exact Interval.inter_mem Dyadic.toRealOrderEmbedding
    (mem_binarySplitMap _ hx fun _ hJ ↦ sinNarrow_mem hJ prec) hC

/-- The cosine of an interval, computed from `sin (I / 2)` by `cos x = 1 - 2 * sin (x / 2) ^ 2`.
`sin (I / 2)` is evaluated at `prec + 3`, one bit more than `cosPoint` uses, for the final
rounding. -/
@[expose]
def cos (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let s := sin ((Interval.singleton ((1 : Dyadic) >>> (1 : ℕ))).mul I) (prec + 3)
  roundOut ((Interval.singleton 1).sub ((Interval.singleton 2).mul (s.pow 2))) (prec + 1)

@[inclusion_op interval_dyadic_real]
theorem cos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cos x ∈ cos I prec := by
  have h1 : (1 : ℝ) ∈ Interval.singleton (1 : Dyadic) := by simpa using natCast_mem 1
  have hh : (2⁻¹ : ℝ) ∈ Interval.singleton ((1 : Dyadic) >>> (1 : ℕ)) := by
    simpa [mem_iff_mem_map, Dyadic.toReal, Dyadic.toRat_shiftRight_nat] using
      Interval.mem_map_singleton ((1 : Dyadic) >>> (1 : ℕ)) Dyadic.toReal
  have h := roundOut_mem
    (sub_mem h1 (mul_mem (ofNat_mem 2) (pow_mem 2 (sin_mem (mul_mem hh hx) (prec + 3))))) (prec + 1)
  rwa [← Real.cos_two_mul_eq_one_sub, mul_inv_cancel_left₀ two_ne_zero] at h

end IntervalDyadicReal

end Inclusion
