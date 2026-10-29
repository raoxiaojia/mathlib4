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
  /-- Proofs `h : Nat.Prime q`, used as the proof of `q` and tried as factors. -/
  proofs : List Nat.Primes := []

/-- The certificate family with its options. -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig := {})

/-- Lets a proof of `Nat.Prime p` stand for an element of `Nat.Primes` in `LucasConfig.proofs`. -/
scoped instance {p : Nat} (h : Nat.Prime p) : CoeDep (Nat.Prime p) h Nat.Primes := ⟨⟨p, h⟩⟩

/-- Configuration for `primality`. -/
structure Config where
  /-- The `CertConfig` value as written, which the tactic elaborates in the goal's context. -/
  cert : Option Term := none

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config where
  option cert := fun cfg item => return { cfg with cert := some ⟨item.value⟩ }

/-- Evaluates `e` to a numeral `n`, and returns `n`, its raw literal `nQ` and a proof of
`IsNat e nQ`. -/
def evalNumeral (e : Q(Nat)) : MetaM (Nat × (nQ : Q(Nat)) × Q(IsNat $e $nQ)) := do
  let ⟨nQ, pn⟩ ← try deriveNat e q(Nat.instAddMonoidWithOne) catch _ =>
    throwError "{e} does not evaluate to a numeral"
  let .lit (.natVal n) := nQ | failure
  return ⟨n, nQ, pn⟩

/-- Reads a proof `h` of `Nat.Prime e`, where `e` evaluates to a numeral `q`, as `q` and the
element of `Nat.Primes` on the raw literal of `q`. -/
def readPrimeProof (e : Q(Nat)) (h : Q(Nat.Prime $e)) : MetaM (Nat × Q(Nat.Primes)) := do
  let ⟨q, qQ, pq⟩ ← evalNumeral e
  return (q, q(⟨$qQ, isNat.natElim (p := fun m ↦ Nat.Prime m → Nat.Prime $qQ) $pq id $h⟩))

open Lean.Elab.ConfigEval.EvalExpr in
/-- Elaborates `cert` against `CertConfig` in the goal's context, where a proof of `Nat.Prime p`
stands for an element of `Nat.Primes`. Returns the context of `provePrime` built from the options,
and the proofs of primality they supply. -/
def elabCertConfig (cert : Term) : TermElabM (Context × Std.HashMap Nat PrimalityResult) := do
  let cert ← `(open scoped Mathlib.Tactic.Primality in $cert)
  let e ← Term.withSynthesize <| Term.elabTermEnsuringType cert (mkConst ``CertConfig)
  let_expr CertConfig.lucas e := ← instantiateMVars e |
    throwError "{e} is not of the form `.lucas \{ … }`"
  let_expr LucasConfig.mk factors roots proofs := e |
    throwError "{e} is not of the form `\{ factors := …, roots := …, proofs := … }`"
  let mut proved : Std.HashMap Nat PrimalityResult := {}
  for p in ← evalListExpr pure proofs do
    let_expr Subtype.mk _ _ n h := p | throwError "{p} is not a proof of `Nat.Prime n`"
    let (q, qQ) ← readPrimeProof n h
    proved := proved.insert q (.ok qQ)
  let factors ← evalListExpr evalNatExpr factors
  let roots ← evalListExpr evalNatExpr roots
  let factorizer := Factorizer.then (.ofArray (proved.keysArray ++ factors.toArray))
    (trialDivision trialDivisionBound)
  let rootFinder :=
    PrimitiveRootFinder.then (.ofArray roots.toArray) (trialRoots primitiveRootBound)
  return ({ factorizer, rootFinder }, proved)

/-- `primality` tries to prove a goal `Nat.Prime n` from the hint provided by the user.
`primality (cert := .lucas { factors := [p₁, …, pₖ] })` tries `p₁, …, pₖ` as prime factors of
`n - 1` and recursively `p - 1` for any intermediate prime value `p` that needs to be proven. The
tactic assumes that the factors provided by the user are prime.
`primality (cert := .lucas { roots := [a₁, …, aₖ] })` tries `a₁, …, aₖ` as primitive roots before
searching for one.
`primality (cert := .lucas { proofs := [h₁, …, hₖ] })` tries the primes `qᵢ` of
`hᵢ : Nat.Prime qᵢ` as factors, and uses `hᵢ` as the proof of `qᵢ` wherever `qᵢ` must be proved
prime. -/
syntax (name := primality) "primality" optConfig : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig) => withMainContext do
    let (ctx, proved) ← elabCertConfig <| ← (← elabPrimalityConfig cfg).cert.getDM `(.lucas)
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := (← instantiateMVars (← g.getType)) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let ⟨p, nn, pn⟩ ← evalNumeral e
      match ← (provePrime p).run ctx |>.run' proved with
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
