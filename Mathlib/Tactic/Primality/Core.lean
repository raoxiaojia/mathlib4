/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Lucas

/-!
# Primality certificates

Certificates of primality from each certificate family, and the function that proves a prime from
them.

TODO: add variants of Pocklington certificates, with the minimal theory they need.
-/

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- A certificate for the primality of one number, from one of the certificate families. -/
inductive Cert where
  /-- A Lucas certificate. -/
  | lucas (w : LucasWitness)

/-- Proves `Nat.Prime p` from the certificates in `certs`, and by `norm_num` below `normNumBound`
for a number without one. The cache holds the proof for each prime, and may start with proofs the
caller already has. -/
partial def certifyPrime (certs : Std.HashMap Nat Cert) (p : Nat) :
    MonadStateCacheT Nat Expr MetaM Q(Nat.Prime $p) :=
  checkCache (β := Expr) p fun _ ↦ do
    match certs[p]? with
    | some (.lucas ⟨a, qs⟩) =>
      return certifyLucas p a (← qs.mapM fun q ↦ return ⟨q, ← certifyPrime certs q⟩)
    | none =>
      unless p < normNumBound do
        throwError "no certificate for {p}"
      let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $p) | throwError "norm_num cannot prove {p} prime"
      return pf

end Mathlib.Tactic.Primality
