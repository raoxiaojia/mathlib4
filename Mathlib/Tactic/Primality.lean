/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Core

/-!
# `primality`

This file defines the `primality` tactic, which closes primality goals `Nat.Prime n` using witnesses
provided for a closed set of primality certificates.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- The bound of the trial division that factors `p - 1`. -/
def trialDivisionBound : Nat := 1024

/-- Primitive roots are tried below this bound. -/
def primitiveRootBound : Nat := 1000

/-- Options for Lucas certificates. -/
structure LucasConfig where
  /-- Candidate prime factors, tried before trial division. -/
  factors : List Nat := []
  /-- Candidate primitive roots, tried before the search. -/
  roots : List Nat := []

/-- The certificate family with its options.
 -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig := {})

/-- Configuration for `primality`. -/
structure Config where
  /-- The certificate family, with its options. -/
  cert : CertConfig := .lucas

open scoped Lean.Elab.ConfigEval in
private local ensure_eval_expr_instance CertConfig

open Lean.Elab.ConfigEval in
/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config where
  -- The derived handler reads `.lucas` from the syntax and rejects it for its missing argument.
  option cert := fun cfg item => do
    return { cfg with cert := ← evalExprWithElab ⟨item.value⟩ }

/-- `primality` tries to prove a goal `Nat.Prime n` from the hint provided by the user.
`primality (cert := .lucas { factors := [p₁, …, pₖ] })` tries `p₁, …, pₖ` as prime factors of
`n - 1` and recursively `p - 1` for any intermediate prime value `p` that needs to be proven. The
tactic assumes that the factors provided by the user are prime.
`primality (cert := .lucas { roots := [a₁, …, aₖ] })` tries `a₁, …, aₖ` as primitive roots before
searching for one. -/
syntax (name := primality) "primality" optConfig : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig) => do
    let .lucas ⟨factors, roots⟩ := (← elabPrimalityConfig cfg).cert
    let factorizer := Factorizer.then (.ofArray factors.toArray)
      (trialDivision trialDivisionBound)
    let rootFinder :=
      PrimitiveRootFinder.then (.ofArray roots.toArray) (trialRoots primitiveRootBound)
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
        if ns.contains p then
          throwError "primality could not find a primitive root of {p}; add explicit roots to \
            `.lucas \{ roots := … }`."
        throwError "primality could not find factors for these intermediate values: \
          {ns.toList.eraseDups}; factors can be explicitly provided at \
          `.lucas \{ factors := … }`. In the rare case that any of the values is prime, add \
          primitive roots of them to `.lucas \{ roots := … }`."

end Mathlib.Tactic.Primality
