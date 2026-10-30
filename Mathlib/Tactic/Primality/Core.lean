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

Certificates of primality, the search that finds one for a prime, and the function that proves a
prime from one.
-/

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 16

/-- The certificate family with its options. -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig)

/-- A certificate that `p` is prime. A certificate that depends on other primes holds their
certificates, which may be shared with other certificates. -/
inductive Cert : Nat → Type where
  /-- `p` is proved prime by `norm_num`. -/
  | normNum {p : Nat} : Cert p
  /-- A proof that `p` is prime is supplied. -/
  | known {p : Nat} : Cert p
  /-- A Lucas certificate with the primitive root `root`, and the prime factors of `p - 1` with
  their certificates in `factors`. -/
  | lucas {p : Nat} (root : Nat) (factors : Array ((q : Nat) × Cert q)) : Cert p

/-- Finds a certificate for `p` with the options in `cfg`, using `Cert.known` for the primes in
`known` and `Cert.normNum` for the primes below `normNumBound`. The search of a certificate family
throws its own error at the first value it cannot certify. -/
partial def findCert (cfg : CertConfig) (known : Std.HashSet Nat) (p : Nat) : CoreM (Cert p) :=
  StateT.run' (go p) {}
where
  /-- Finds a certificate for `q`. The state holds the Lucas certificates found so far, shared by
  every certificate that depends on them. -/
  go (q : Nat) : StateT (Std.DHashMap Nat Cert) CoreM (Cert q) := do
    if let some cert := (← get).get? q then
      return cert
    if known.contains q then
      return .known
    if q < normNumBound then
      return .normNum
    match cfg with
    | .lucas lucasCfg =>
      let factorizer := (Factorizer.ofArray known.toArray).then lucasCfg.toFactorizer
      let w ← findLucasWitness factorizer lucasCfg.toPrimitiveRootFinder p q
      let cert : Cert q := .lucas w.root (← w.factors.mapM fun r ↦ return ⟨r, ← go r⟩)
      modify (·.insert q cert)
      return cert

/-- Proves `Nat.Prime p` from the certificate `cert`. The cache holds the proof of each prime, so
that a prime is proved once however many certificates depend on it, and starts with the proofs of
the primes that are `Cert.known`. -/
partial def certifyPrime {p : Nat} (cert : Cert p) :
    MonadStateCacheT Nat Expr MetaM Q(Nat.Prime $p) :=
  checkCache (β := Expr) p fun _ ↦ do
    match cert with
    | .normNum =>
      let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $p) | throwError "norm_num cannot prove {p} prime"
      return pf
    | .known => throwError "no proof that {p} is prime is supplied"
    | .lucas root factors =>
      return certifyLucas p root (← factors.mapM fun ⟨q, cert⟩ ↦ return ⟨q, ← certifyPrime cert⟩)

end Mathlib.Tactic.Primality
