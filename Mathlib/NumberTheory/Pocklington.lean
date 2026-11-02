/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Multiplicity

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.ChineseRemainder

/-! # Pocklington's primality certificate

To use this certificate for primality of `N`, factorise `N - 1` completely.
1. If the largest factor `p` is `> √N`, then set `F₁ = p`.
2. Otherwise, set `F₁` to be the product of enough prime factors to be `> √N`.
3. Then, find a primitive root `a` of `N`.
4. Then `a` will satisfy the conditions required, which are:
  - `a ^ (N - 1) ≡ 1 (mod N)`
  - For each prime factor `p` of `F₁`, `gcd(a ^ ((N - 1) / p) - 1, N) = 1`.
-/

theorem Nat.modEq_finset_prod_iff {a b : ℕ} {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (co : (s : Set ι).Pairwise (Coprime.onFun e)) :
    a ≡ b [MOD ∏ i ∈ s, e i] ↔ ∀ i ∈ s, a ≡ b [MOD e i] := by
  classical
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  rw [List.prod_toFinset e hl, Nat.modEq_list_map_prod_iff]
  · simp_rw [List.mem_toFinset]
  · rwa [← List.pairwise_iff_coe_toFinset_pairwise hl]

public theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} (hn₀ : n ≠ 0) :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  conv_lhs => rw [← prod_factorization_pow_eq_self hn₀]
  rw [Finsupp.prod, modEq_finset_prod_iff]
  · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
    refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
    rw [multiplicity_eq_factorization hp]
  · grind [support_factorization, coprime_pow_primes, Set.Pairwise]

public theorem Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div
    {q n x : ℕ} (hq : q.Prime) (hxn : x ∣ n) (hxnq : ¬ x ∣ n / q) :
    q ^ multiplicity q n ∣ x := by
  by_cases hqn : q ∣ n
  · obtain ⟨n, rfl⟩ := hqn
    rw [Nat.mul_div_cancel_left _ hq.pos] at hxnq
    by_cases hn₀ : n = 0
    · subst hn₀; exact (hxnq <| dvd_zero _).elim
    have hqn₀ : q * n ≠ 0 := mul_ne_zero hq.ne_zero hn₀
    have hx₀ : x ≠ 0 := by rintro rfl; exact hqn₀ <| zero_dvd_iff.mp hxn
    rw [← Nat.factorization_le_iff_dvd hx₀ hn₀] at hxnq
    rw [← Nat.factorization_le_iff_dvd hx₀ hqn₀] at hxn
    rw [Nat.factorization_mul hq.ne_zero hn₀, hq.factorization, add_comm] at hxn
    refine pow_dvd_of_le_multiplicity ?_
    rw [multiplicity_eq_factorization hq, multiplicity_eq_factorization hq,
      Nat.factorization_mul hq.ne_zero hn₀, Finsupp.add_apply, hq.factorization,
      Finsupp.single_apply, ite_eq_left rfl, add_comm]
    refine le_of_not_gt fun h ↦ hxnq fun p ↦ ?_
    by_cases hpq : p = q
    · subst hpq; exact Nat.lt_succ_iff.mp h
    convert hxn p using 1
    rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hpq), add_zero]
  · rw [multiplicity_eq_zero_of_not_dvd hqn, pow_zero]
    exact one_dvd _

/-- Let `N` be a natural number whose primality we want to certify.
Assume we have a partial factorisation `N - 1 = F₁ * R₁`, where `F₁` is fully factorised with
prime factors `pᵢ`.
Now for each `pᵢ` find a pseudo-primitive root `aᵢ` such that `aᵢ ^ (N - 1) ≡ 1 (mod N)` and
`gcd(aᵢ ^ ((N - 1) / pᵢ) - 1, N) = 1`.
Then any prime factor `n` of `N` satisfies `n ≡ 1 (mod F₁)`. -/
public theorem pocklington_test (N F₁ : ℕ) (hn₀ : 0 < N) (hf₁ : F₁ ∣ N - 1)
    (primitive : ∀ p ∈ F₁.primeFactors, ∃ a : ℕ, a ^ (N - 1) ≡ 1 [MOD N] ∧
      Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1)
    (p : ℕ) (hp : p.Prime) (hpn : p ∣ N) : p ≡ 1 [MOD F₁] := by
  by_cases hn₁ : N = 1
  · rw [hn₁, Nat.dvd_one] at hpn
    exact absurd (hpn ▸ hp) Nat.not_prime_one
  -- `omega` is >2x faster than `lia` here (56ms vs 144ms median over 5 runs)
  replace hn₁ : 1 < N := by omega
  have hf₀ : F₁ ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hf₁
    omega
  rw [Nat.modEq_iff_forall_prime_dvd hf₀]
  intro q hqf hq
  have := Fact.mk hp
  have := (Nat.prime_iff_card_units _).mp hp
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hp.one_le, ← this]
  obtain ⟨a, han, hanq⟩ := primitive q (Nat.mem_primeFactors.mpr ⟨hq, hqf, hf₀⟩)
  have hanp := han.of_dvd hpn
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at hanp
  let a' : (ZMod p)ˣ := Units.ofPowEqOne _ _ hanp (by grind)
  refine dvd_trans ?_ (orderOf_dvd_card (x := a'))
  have : multiplicity q F₁ ≤ multiplicity q (N - 1) := by
    rw [Nat.multiplicity_eq_factorization hq, Nat.multiplicity_eq_factorization hq]
    exact (Nat.factorization_le_iff_dvd hf₀ (by grind)).mpr hf₁ _
  refine dvd_trans (pow_dvd_pow _ this) ?_
  refine Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div hq ?_ ?_
  · rwa [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
  · rw [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
    unfold a'
    have : 1 ≤ a ^ ((N - 1) / q) := Nat.one_le_pow _ _ <| pos_of_ne_zero fun ha₀ ↦ by
      subst ha₀; rw [Nat.cast_zero, zero_pow (by grind)] at hanp; simp at hanp
    rw [Units.val_ofPowEqOne, ← Nat.cast_pow, Units.val_one, ← Nat.cast_one (R := ZMod p),
      ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' this,
      ← hp.coprime_iff_not_dvd]
    rw [← Nat.coprime_iff_gcd_eq_one] at hanq
    exact hanq.symm.coprime_dvd_left hpn

/-- The Pocklington primitive-root predicate: for each prime factor `p` of `F₁`,
`gcd(root ^ ((N-1)/p) - 1, N) = 1`. Built incrementally by `PocklingtonPred.step`. -/
@[expose] public def PocklingtonPred (N root F₁ : ℕ) : Prop :=
  ∀ p ∈ F₁.primeFactors, (root ^ ((N - 1) / p) - 1).gcd N = 1

public theorem pocklington_certify (N F₁ : ℕ) (h2n : 2 ≤ N) (hf₁ : F₁ ∣ N - 1) (hf₁' : N.sqrt < F₁)
    (root : ℕ) (psp : root ^ (N - 1) ≡ 1 [MOD N])
    (primitive : PocklingtonPred N root F₁) :
    Nat.Prime N := by
  by_contra hn
  rw [Nat.sqrt_lt, ← sq] at hf₁'
  have := pocklington_test N F₁ (by grind) hf₁ (fun p hp ↦ ⟨root, psp, primitive p hp⟩)
    N.minFac (N.minFac_prime (by grind)) N.minFac_dvd
  have h1p : 2 ≤ N.minFac := (N.minFac_prime (by grind)).two_le
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by grind)] at this
  have := Nat.succ_le_iff.mp <| (Nat.le_sub_iff_add_le (by grind)).mp <|
    Nat.le_of_dvd (by grind) this
  exact lt_asymm hf₁' <| ((Nat.pow_lt_pow_iff_left (by grind)).mpr this).trans_le <|
    Nat.minFac_sq_le_self (by grind) hn
