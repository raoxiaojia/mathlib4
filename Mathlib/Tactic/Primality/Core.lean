/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Factorizer
public import Mathlib.Tactic.Primality.Lucas

/-!
# Primality certificates from factorisations of `p - 1`

Proves `Nat.Prime p` by a tree of certificates, one for `p` and one for each prime factor of
`p - 1` that it uses, and finds the prime factors with a factorizer.

TODO: add a minimal set of theory required for variants of Pocklington certificate and implement
a certifier based on that.
-/

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

/-- What `provePrime` reads. -/
structure Context where
  /-- Finds the prime factors of `p - 1`. -/
  factorizer : Factorizer
  /-- Finds a primitive root of `p` from the prime factors of `p - 1`. -/
  rootFinder : PrimitiveRootFinder

/-- The outcome of `provePrime` for one number: its proof of primality, or the numbers whose
primality blocked it. -/
abbrev PrimalityResult := Except (Array Nat) Q(Nat.Primes)

/-- The monad of `provePrime`. It reads the `Context`, and its state holds, for each number tried,
its proof of primality or the numbers whose primality blocked it. -/
abbrev PrimalityM := ReaderT Context <| StateT (Std.HashMap Nat PrimalityResult) MetaM

/-- Proves `Nat.Prime pQ` for the raw literal `pQ` of `p`, or returns the numbers whose primality
it could not decide. A part of `p - 1` that the factorizer leaves is taken to be prime and proved
in turn. It reuses the results in the state and records the ones it computes. -/
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
      let some a ← ctx.rootFinder p qs | return .error #[p]
      if Nat.powMod a (p - 1) p != 1 then
        return .error #[p]
      pure (.lucas a qs)
    match cert with
    | .normNum =>
      let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $pQ) | return .error #[p]
      return .ok q(⟨$pQ, $pf⟩)
    | .lucas a qs =>
      let mut factors := #[]
      let mut undecided := #[]
      for q in qs do
        match ← provePrime q with
        | .ok qQ => factors := factors.push (q, qQ)
        | .error ns => undecided := undecided ++ ns
      unless undecided.isEmpty do
        return .error undecided
      return .ok q(⟨$pQ, $(certifyLucas p a pQ factors)⟩) : PrimalityM PrimalityResult)
  modify (·.insert p result)
  return result

end Mathlib.Tactic.Primality
