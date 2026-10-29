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
# Primality certificates from factorizations of `p - 1`

Proves `Nat.Prime p` by a tree of certificates, one for `p` and one for each prime factor of
`p - 1` that it uses, and finds the prime factors with a factorizer.

TODO: add variants of Pocklington certificates, with the minimal theory they need.
-/

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- A primality certificate. -/
inductive Cert where
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

/-- The proof of primality of a number, or the numbers whose primality blocked it. -/
abbrev PrimalityResult := Except (Array Nat) Q(Nat.Primes)

/-- The monad of `provePrime`, whose state holds the result for each number tried. -/
abbrev PrimalityM := ReaderT Context <| MonadStateCacheT Nat PrimalityResult MetaM

/-- Proves `p` prime by an element of `Nat.Primes` on the raw literal of `p`, or returns the numbers
it could not prove prime. The part of `p - 1` that the factorizer leaves is taken to be prime and
proved in turn. -/
partial def provePrime (p : Nat) : PrimalityM PrimalityResult :=
  checkCache p fun _ ↦ do
    checkSystem "primality"
    have pQ : Q(Nat) := mkRawNatLit p
    let cert : Cert ← if p < normNumBound then pure .normNum else
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
      let results ← qs.mapM provePrime
      let .ok hqs := results.mapM id |
        return .error (results.flatMap fun | .ok _ => #[] | .error ns => ns)
      return .ok q(⟨$pQ, $(certifyLucas p a pQ (qs.zip hqs))⟩)

end Mathlib.Tactic.Primality
