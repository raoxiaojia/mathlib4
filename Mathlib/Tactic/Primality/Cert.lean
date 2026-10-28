/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Factorizer

import Mathlib.NumberTheory.LucasPrimality

/-!
# Primality certificates from factorisations of `p - 1`

Constructs a proof of `Nat.Prime p` from a primitive root `a` and the prime factors of `p - 1`, by
the Lucas test, and finds the prime factors with a factorizer.

TODO: add a minimal set of theory required for variants of Pocklington certificate and implement
a certifier based on that.
-/

public section

namespace Mathlib.Tactic.Primality

/-- `lucasCheck p a fs` checks that `a ^ (p - 1) % p = 1`, that `a ^ ((p - 1) / q) % p ≠ 1` for
each `(q, e) ∈ fs`, and that the `q ^ e` multiply to `p - 1`. -/
@[expose] def lucasCheck (p a : ℕ) (fs : List (Nat.Primes × ℕ)) : Bool :=
  Nat.powMod a (p - 1) p == 1 && fs.all (fun f ↦ Nat.powMod a ((p - 1) / f.1) p != 1) &&
    (fs.map fun f ↦ (f.1 : ℕ) ^ f.2).prod == p - 1

theorem prime_of_lucasCheck {p a : ℕ} {fs : List (Nat.Primes × ℕ)}
    (h : lucasCheck p a fs = true) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨ha, hpow⟩, hprod⟩ := h
  have hp : p ≠ 1 := by
    rintro rfl
    simp [Nat.powMod_def] at ha
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← Nat.powMod_def, ha, Nat.cast_one]
  · obtain ⟨_, hx, hqf⟩ := hq.prime.dvd_prod_iff.mp (hprod ▸ hqp)
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq f.1.prop).mp (hq.dvd_of_dvd_pow hqf)
    apply hpow f hf
    rw [Nat.powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' hp]

end Mathlib.Tactic.Primality

end

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- A certificate for the primality of one number, referring to the primes it depends on by
value. -/
inductive Cert (p : Nat) where
  /-- `p` is proved prime by `norm_num`'s evaluation of `Nat.minFac p`. -/
  | normNum
  /-- `p` is proved prime from the primitive root `a` and the prime factors `qs` of `p - 1`. -/
  | lucas (a : Nat) (qs : Array Nat)

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 18

/-- A primitive root finding function. Given `p` and the prime factors `qs` of `p - 1`, it returns
either a primitive root mod `p` or a witness that `p` is composite by `a ^ (p - 1) % p ≠ 1`. -/
abbrev PrimitiveRootFinder := Nat → Array Nat → CoreM (Option Nat)

/-- Tries the candidates `roots` in order, each reduced modulo `p`. -/
def PrimitiveRootFinder.ofArray (roots : Array Nat) : PrimitiveRootFinder := fun p qs ↦ do
  for a in roots do
    let a := a % p
    if a != 0 && (Nat.powMod a (p - 1) p != 1 ||
        qs.all fun q ↦ Nat.powMod a ((p - 1) / q) p != 1) then
      return some a
  return none

/-- Runs `f₁`, followed by `f₂` if `f₁` finds nothing. -/
def PrimitiveRootFinder.then (f₁ f₂ : PrimitiveRootFinder) : PrimitiveRootFinder := fun p qs ↦ do
  if let some a ← f₁ p qs then
    return some a
  f₂ p qs

/-- Simple trial that finds primitive roots up to `bound`. -/
def trialRoots (bound : Nat) : PrimitiveRootFinder :=
  .ofArray (Array.range' 2 (bound - 2))

/-- Proves `Nat.Prime pQ` for the raw literal `pQ` by `norm_num`'s `Nat.Prime` extension, and
throws an error when `pQ` is not prime. -/
def certifyNormNum (pQ : Q(Nat)) : MetaM Q(Nat.Prime $pQ) := do
  let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $pQ) | throwError "{pQ} is not prime"
  return pf

/-- What `provePrime` reads. -/
structure Context where
  /-- Finds the prime factors of `p - 1`. -/
  factorizer : Factorizer
  /-- Finds a primitive root of `p` from the prime factors of `p - 1`. -/
  rootFinder : PrimitiveRootFinder

/-- The outcome of `provePrime` for one number: its proof of primality, or the numbers whose
primality blocked it, each with whether it was shown not to be prime. -/
abbrev PrimalityResult := Except (Array (Nat × Bool)) Q(Nat.Primes)

/-- The monad of `provePrime`. It reads the `Context`, and its state holds, for each number tried,
its proof of primality or the numbers whose primality blocked it. -/
abbrev PrimalityM := ReaderT Context <| StateT (Std.HashMap Nat PrimalityResult) MetaM

/-- Proves `Nat.Prime p` for the raw literal `p` from the primitive root `a` and the prime factors
`qs` of `p - 1`, whose proofs of primality are in the state. -/
def certifyLucas (p a : Nat) (pQ : Q(Nat)) (qs : Array Nat) : PrimalityM Q(Nat.Prime $pQ) := do
  let factors ← qs.toList.mapM fun (q : Nat) ↦ do
    let some (.ok qQ) := (← get)[q]? | throwError "{q} has no proof of primality"
    have expQ : Q(Nat) := mkRawNatLit (Nat.maxPowDvdDiv q (p - 1)).1
    return q(($qQ, $expQ))
  let factorization : Q(List (Nat.Primes × Nat)) := mkListLitQ factors
  have hcheck : Q(lucasCheck $pQ $a $factorization = true) := (q(Eq.refl true) : Expr)
  return q(prime_of_lucasCheck $hcheck)

/-- Proves `Nat.Prime pQ` for the raw literal `pQ` of `p`, or returns the numbers whose primality
it could not decide, each with whether it was shown not to be prime. A part of `p - 1` that the
factorizer leaves is taken to be prime and proved in turn. It reuses the results in the state and
records the ones it computes. -/
partial def provePrime (p : Nat) : PrimalityM PrimalityResult := do
  if let some result := (← get)[p]? then
    return result
  -- The parenthesised block keeps each `return` inside it, so every outcome is recorded below.
  let result ← (do
    checkSystem "primality"
    have pQ : Q(Nat) := mkRawNatLit p
    let cert : Cert p ← if p < normNumBound then pure .normNum else
      let ctx ← read
      let (qs, rest) ← ctx.factorizer.decompose (p - 1)
      let qs := if rest == 1 then qs else qs.push rest
      let some a ← ctx.rootFinder p qs | return .error #[(p, false)]
      if Nat.powMod a (p - 1) p != 1 then
        return .error #[(p, true)]
      pure (.lucas a qs)
    match cert with
    | .normNum => return .ok q(⟨$pQ, $(← certifyNormNum pQ)⟩)
    | .lucas a qs =>
      let mut undecided := #[]
      for q in qs do
        if let .error ns ← provePrime q then
          undecided := undecided ++ ns
      unless undecided.isEmpty do
        return .error undecided
      return .ok q(⟨$pQ, $(← certifyLucas p a pQ qs)⟩) : PrimalityM PrimalityResult)
  modify (·.insert p result)
  return result

end Mathlib.Tactic.Primality
