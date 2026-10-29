/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Core

/-!
# `primality`

This file defines the `primality` tactic, which closes goals `Nat.Prime n` using a closed set of
primality certificates, with witnesses it finds itself or takes from hints.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum Lean.Elab.ConfigEval

namespace Mathlib.Tactic.Primality

/-- Options for Lucas certificates. -/
structure LucasConfig extends FactorizerConfig, PrimitiveRootFinderConfig where
  /-- Proofs `h : Nat.Prime q`, used as the proof of `q` and tried as factors. -/
  proofs : List Nat.Primes := []

/-- The certificate family with its options. -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig := {})

namespace CertConfig

/-- Lets a proof of `Nat.Prime p` stand for an element of `Nat.Primes` in `LucasConfig.proofs`. -/
scoped instance {p : Nat} (h : Nat.Prime p) : CoeDep (Nat.Prime p) h Nat.Primes := ⟨⟨p, h⟩⟩

end CertConfig

/-- Configuration for `primality`. -/
structure Config where
  /-- The `CertConfig` value as written, which the tactic elaborates in the goal's context. -/
  cert : Option Term := none

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config where
  option cert := fun cfg item => return { cfg with cert := some ⟨item.value⟩ }

/-- Evaluates `e` to a numeral with `norm_num`. -/
def evalNumeral (e : Q(Nat)) : MetaM (Nat × (nQ : Q(Nat)) × Q(IsNat $e $nQ)) := do
  let ⟨nQ, pn⟩ ← try deriveNat e q(Nat.instAddMonoidWithOne) catch _ =>
    throwError "{e} does not evaluate to a numeral; try simplifying it first"
  let .lit (.natVal n) := nQ | failure
  return ⟨n, nQ, pn⟩

private local ensure_eval_expr_instance FactorizerConfig
private local ensure_eval_expr_instance PrimitiveRootFinderConfig

open Lean.Elab.ConfigEval.EvalExpr in
/-- Elaborates `cert` against `CertConfig` in the goal's context. Returns the context of
`provePrime` built from the options, and the proofs of primality they supply. -/
def elabCertConfig (cert : Term) : TermElabM (Context × Std.HashMap Nat PrimalityResult) := do
  let cert ← `(open scoped Mathlib.Tactic.Primality.CertConfig in $cert)
  let e ← Term.withSynthesize <| Term.elabTermEnsuringType cert (mkConst ``CertConfig)
  let_expr CertConfig.lucas e := ← instantiateMVars e |
    throwError "{e} is not of the form `.lucas \{ … }`"
  let_expr LucasConfig.mk factorizerCfg rootFinderCfg proofs := e |
    throwError "{e} is not of the form `\{ … }`"
  let mut proved : Std.HashMap Nat PrimalityResult := {}
  for p in ← evalListExpr pure proofs do
    let_expr Subtype.mk _ _ n h := p | throwError "{p} is not a proof of `Nat.Prime n`"
    have n : Q(Nat) := n
    have h : Q(Nat.Prime $n) := h
    let ⟨q, qQ, pq⟩ ← evalNumeral n
    proved := proved.insert q <|
      .ok q(⟨$qQ, isNat.natElim (p := fun m ↦ Nat.Prime m → Nat.Prime $qQ) $pq id $h⟩)
  let factorizerCfg : FactorizerConfig ← evalExpr factorizerCfg
  let rootFinderCfg : PrimitiveRootFinderConfig ← evalExpr rootFinderCfg
  let factorizer := (Factorizer.ofArray proved.keysArray).then factorizerCfg.toFactorizer
  return ({ factorizer, rootFinder := rootFinderCfg.toRootFinder }, proved)

/-- `primality` tries to prove a goal `Nat.Prime n`, using the hints provided by the user if any.
`primality (cert := .lucas { … })` passes hints and options to Lucas certificates, such as prime
factors of `n - 1` (see `LucasConfig`). -/
syntax (name := primality) "primality" optConfig : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig) => withMainContext do
    let (ctx, proved) ← elabCertConfig <| ← (← elabPrimalityConfig cfg).cert.getDM `(.lucas)
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := (← instantiateMVars (← g.getType)) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let ⟨p, pQ, pn⟩ ← evalNumeral e
      match ← StateT.run' ((provePrime p).run ctx) proved with
      | .ok hp =>
        have : $pQ =Q ($hp).1 := ⟨⟩
        g.assign q(isNat.natElim (p := Nat.Prime) $pn ($hp).2)
      | .error ns =>
        if ns.contains p then
          throwError "primality is unable to find a primitive root for {p}; \
            primitive roots can be provided at `.lucas \{ roots := … }` if {p} is prime."
        throwError "primality could not find factors for these intermediate values: \
          {ns.toList.eraseDups}; factors can be provided at \
          `.lucas \{ factors := … }`. In the rare case that any of the values is prime, add \
          primitive roots of them to `.lucas \{ roots := … }`."

end Mathlib.Tactic.Primality
