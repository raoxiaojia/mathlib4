/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/
module

public import Mathlib.NumberTheory.Pocklington
public import Mathlib.Tactic.Primality.PowMod
public import Mathlib.Tactic.Primality.PredMod

/-! # Kernel-checked Pocklington certificates

The lemmas the `pock` certificate method emits. `PocklingtonPred` is built one prime power of `F₁`
at a time, and each condition is a `Bool` the kernel evaluates.
-/

public theorem pocklington_certifyK (N root F₁ : ℕ)
    (primitive : PocklingtonPred N root F₁)
    (psp : (powModK root N.pred N).beq 1)
    (h2n : Nat.ble 2 N)
    (hf₁ : (N.pred.mod F₁).beq 0)
    (hf₁' : N.blt (F₁.mul F₁)) : N.Prime := by
  simp_all only [powModK_eq, Nat.beq_eq, Nat.ble_eq, Nat.mod_eq_mod,
    ← Nat.dvd_iff_mod_eq_zero, Nat.mul_eq, Nat.blt_eq, ← Nat.sqrt_lt]
  rw [← Nat.one_mod_eq_one.mpr (show N ≠ 1 by lia)] at psp
  exact pocklington_certify N F₁ h2n hf₁ hf₁' root psp primitive

@[simp] theorem PocklingtonPred.zero {N root : ℕ} :
    PocklingtonPred N root 0 := by
  simp [PocklingtonPred]

@[simp] public theorem PocklingtonPred.one {N root : ℕ} :
    PocklingtonPred N root 1 := by
  simp [PocklingtonPred]

public theorem PocklingtonPred.step_pow {N root F₂ p e : ℕ} (hp : p.Prime)
    (ih : PocklingtonPred N root F₂)
    (step : ((predModK (powModK root (N.pred.div p) N) N).gcd N).beq 1)
    (hroot : Nat.blt 0 root = true) :
    PocklingtonPred N root (F₂.mul (p.pow e)) := by
  by_cases hf₂ : F₂ = 0
  · simp [hf₂]
  by_cases he : e = 0
  · simpa [he]
  by_cases hn : N = 0
  · simp [hn, predModK, powModK_eq] at step
  rw [PocklingtonPred] at ih ⊢
  rw [Nat.mul_eq, Nat.pow_eq]
  rw [Nat.primeFactors_mul hf₂ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow he hp]
  simp_rw [Finset.union_singleton, Finset.forall_mem_insert]
  refine ⟨?_, ih⟩
  simp only [Nat.pred_eq_sub_one, Nat.div_eq_div, Nat.beq_eq] at step
  simp only [Nat.blt_eq] at hroot
  rw [predModK_eq hn (by rw [powModK_eq]; exact (Nat.mod_lt _ (by lia)).le),
    ← Nat.add_sub_assoc (by lia), powModK_eq] at step
  by_cases hp : root ^ ((N - 1) / p) % N = 0
  · rw [← Nat.dvd_iff_mod_eq_zero] at hp
    obtain ⟨r, hr⟩ := hp
    have : r ≠ 0 := by rintro rfl; rw [mul_zero, pow_eq_zero_iff'] at hr; lia
    replace this := mul_ne_zero hn this
    rw [hr, Nat.gcd_mul_left_sub_left (by lia), Nat.gcd_one_left]
  rwa [add_comm, Nat.add_sub_assoc (by lia), Nat.add_mod_left, Nat.mod_sub_of_le (by lia),
    Nat.mod_mod, ← Nat.gcd_rec, Nat.gcd_comm] at step

public theorem PocklingtonPred.step {N root F₂ p : ℕ} (hp : p.Prime)
    (ih : PocklingtonPred N root F₂)
    (step : ((predModK (powModK root (N.pred.div p) N) N).gcd N).beq 1)
    (hroot : Nat.blt 0 root = true) :
    PocklingtonPred N root (F₂.mul p) := by
  simpa using PocklingtonPred.step_pow (e := 1) hp ih step hroot

public theorem PocklingtonPred.base_pow {N root p e : ℕ} (hp : p.Prime)
    (step : ((predModK (powModK root (N.pred.div p) N) N).gcd N).beq 1)
    (hroot : Nat.blt 0 root = true) :
    PocklingtonPred N root (p.pow e) := by
  simpa using PocklingtonPred.step_pow hp .one step hroot

public theorem PocklingtonPred.base {N root p : ℕ} (hp : p.Prime)
    (step : ((predModK (powModK root (N.pred.div p) N) N).gcd N).beq 1)
    (hroot : Nat.blt 0 root = true) :
    PocklingtonPred N root p := by
  simpa using PocklingtonPred.base_pow (e := 1) hp step hroot
