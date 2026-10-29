/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public meta import Mathlib.Util.Qq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Primality.Producers

import Mathlib.NumberTheory.LucasPrimality

/-!
# Lucas primality certificates

Proves `Nat.Prime p` by the Lucas test from a primitive root and certified prime factors of `p - 1`.
-/

public section

namespace Mathlib.Tactic.Primality

/-- `b ^ e % m`, computed four bits of `e` at a time by `Nat.pow`, which the kernel evaluates
natively. Replace it with `Nat.powMod` once the kernel evaluates `Nat.powMod` efficiently. -/
@[expose] def powMod (b e m : ℕ) : ℕ :=
  if e = 0 then 1 % m else powMod b (e / 16) m ^ 16 * b ^ (e % 16) % m
termination_by e
decreasing_by lia

theorem powMod_def (b e m : ℕ) : powMod b e m = b ^ e % m := by
  fun_induction powMod b e m with
  | case1 => simp
  | case2 e _ ih =>
    rw [ih, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod, ← Nat.pow_mul, ← Nat.pow_add,
      Nat.div_add_mod']

/-- `lucasCheck p a fs` checks that `a ^ (p - 1) % p = 1`, that `a ^ ((p - 1) / q) % p ≠ 1` for
each `(q, e) ∈ fs`, and that the `q ^ e` multiply to `p - 1`. -/
@[expose] def lucasCheck (p a : ℕ) (fs : List (Nat.Primes × ℕ)) : Bool :=
  powMod a (p - 1) p == 1 && fs.all (fun f ↦ powMod a ((p - 1) / f.1) p != 1) &&
    (fs.map fun f ↦ (f.1 : ℕ) ^ f.2).prod == p - 1

theorem prime_of_lucasCheck {p a : ℕ} {fs : List (Nat.Primes × ℕ)}
    (h : lucasCheck p a fs = true) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨ha, hpow⟩, hprod⟩ := h
  have hp : p ≠ 1 := by
    rintro rfl
    simp [powMod_def] at ha
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← powMod_def, ha, Nat.cast_one]
  · obtain ⟨_, hx, hqf⟩ := hq.prime.dvd_prod_iff.mp (hprod ▸ hqp)
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq f.1.prop).mp (hq.dvd_of_dvd_pow hqf)
    apply hpow f hf
    rw [powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' hp]

end Mathlib.Tactic.Primality

end

public meta section

open Lean Qq

namespace Mathlib.Tactic.Primality

/-- A Lucas certificate for `p`. -/
structure LucasWitness where
  /-- A primitive root of `p`. -/
  a : Nat
  /-- The prime factors of `p - 1`. -/
  qs : Array Nat

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 18

/-- Proves `Nat.Prime p` from the primitive root `a` and the prime factors of `p - 1` in `factors`,
each with its proof of primality. -/
def certifyLucas (p a : Nat) (factors : Array ((q : Nat) × Q(Nat.Prime $q))) : Q(Nat.Prime $p) :=
  let factorization : Q(List (Nat.Primes × Nat)) := mkListLitQ <| factors.toList.map fun ⟨q, hq⟩ ↦
    have expQ : Q(Nat) := mkRawNatLit (Nat.maxPowDvdDiv q (p - 1)).1
    q((⟨$q, $hq⟩, $expQ))
  -- The kernel evaluates `Nat` arithmetic on terms with free variables (such as a hypothesis
  -- proving one of the factors prime) only inside `eagerReduce`.
  have hcheck : Q(lucasCheck $p $a $factorization = true) := eagerReflBoolTrue
  q(prime_of_lucasCheck $hcheck)

/-- Searches for Lucas certificates of `p` and of the primes it depends on, recording them in the
state, or returns the numbers whose primality blocked the search. Numbers below `normNumBound` are
left to `norm_num`, and the numbers in `known` need no certificate. The part of `p - 1` that the
factorizer leaves is taken to be prime and certified in turn. -/
partial def findLucasCerts (factorizer : Factorizer) (rootFinder : PrimitiveRootFinder)
    (known : Std.HashMap Nat Expr) (p : Nat) :
    StateT (Std.HashMap Nat LucasWitness) CoreM (Array Nat) := do
  if known.contains p || (← get).contains p then return #[]
  checkSystem "primality"
  if p < normNumBound then
    return if isProbablePrime p then #[] else #[p]
  let (qs, rest) ← factorizer.decompose (p - 1)
  let qs := if rest == 1 then qs else qs.push rest
  let some a ← rootFinder p qs | return #[p]
  if Nat.powMod a (p - 1) p != 1 then
    return #[p]
  let mut blocked := #[]
  for q in qs do
    blocked := blocked ++ (← findLucasCerts factorizer rootFinder known q)
  if blocked.isEmpty then
    modify (·.insert p ⟨a, qs⟩)
  return blocked

end Mathlib.Tactic.Primality
