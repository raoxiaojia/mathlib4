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
def trialBound : Nat := 65536

/-- Configuration for `primality`. -/
structure Config where
  /-- Candidate prime factors, tried before trial division. -/
  factors : List Nat := []

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config

/-- `primality` proves a goal `Nat.Prime n`, where `n` evaluates to a numeral, with a Pratt
certificate. It factors `n - 1` by trial division. `primality (factors := [q₁, …, qₖ])` also tries
`q₁, …, qₖ` as prime factors of `n - 1`, and of `q - 1` for the primes `q` it certifies on the
way. The user is responsible for ensuring that the supplied values are prime. -/
syntax (name := primality) "primality" optConfig : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig) => do
    let cfg ← elabPrimalityConfig cfg
    let factorizer := Factorizer.then (.ofArray cfg.factors.toArray) (trialDivision trialBound)
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := (← instantiateMVars (← g.getType)) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let ⟨nn, pn⟩ ← try deriveNat e q(Nat.instAddMonoidWithOne) catch _ =>
        throwError "{e} does not evaluate to a numeral"
      let .lit (.natVal p) := nn | failure
      let (_, certs) ← (findCerts factorizer p).run #[]
      let proofs ← certify certs
      let some ⟨pQ, pf⟩ := proofs[p]? | failure
      have : $nn =Q $pQ := ⟨⟩
      g.assign q(isNat.natElim (p := Nat.Prime) $pn $pf)

end Mathlib.Tactic.Primality
