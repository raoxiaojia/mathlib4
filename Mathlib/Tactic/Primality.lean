/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Cert

/-!
# `primality`

This file defines the `primality` tactic, which closes primality goals `Nat.Prime n` using witnesses
provided for a closed set of primality certificates.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- The bound of the trial division that factors `p - 1`. -/
def trialBound : Nat := 1024

/-- Primitive roots are tried below this bound. -/
def primitiveRootBound : Nat := 1000

/-- Configuration for `primality`. -/
structure Config where
  /-- Candidate prime factors, tried before trial division. -/
  factors : List Nat := []
  /-- Candidate primitive roots, tried before the search. -/
  roots : List Nat := []

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config

/-- `primality` proves a goal `Nat.Prime n`, where `n` evaluates to a numeral, with a Pratt
certificate. It factors `n - 1` by trial division. `primality (factors := [q₁, …, qₖ])` also tries
`q₁, …, qₖ` as prime factors of `n - 1`, and of `q - 1` for the primes `q` it certifies on the
way. The user is responsible for ensuring that the supplied values are prime.
`primality (roots := [a₁, …, aₖ])` tries `a₁, …, aₖ` as primitive roots before searching for one. -/
syntax (name := primality) "primality" optConfig : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig) => do
    let cfg ← elabPrimalityConfig cfg
    let factorizer := Factorizer.then (.ofArray cfg.factors.toArray) (trialDivision trialBound)
    let rootFinder :=
      PrimitiveRootFinder.then (.ofArray cfg.roots.toArray) (trialRoots primitiveRootBound)
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := (← instantiateMVars (← g.getType)) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let ⟨nn, pn⟩ ← try deriveNat e q(Nat.instAddMonoidWithOne) catch _ =>
        throwError "{e} does not evaluate to a numeral"
      let .lit (.natVal p) := nn | failure
      match ← (provePrime p).run { factorizer, rootFinder } |>.run' {} with
      | .ok pQ =>
        have : $nn =Q ($pQ).1 := ⟨⟩
        g.assign q(isNat.natElim (p := Nat.Prime) $pn ($pQ).2)
      | .error ns =>
        if ns.contains (p, true) then
          throwError "{p} is not prime"
        throwError "primality could not determine whether these numbers, needed to certify {p}, \
          are prime: {(ns.map (·.1)).toList.eraseDups}. For each of them, add a prime factor of it \
          to `factors` if it is not prime, or a primitive root of it to `roots` if it is prime."

end Mathlib.Tactic.Primality
