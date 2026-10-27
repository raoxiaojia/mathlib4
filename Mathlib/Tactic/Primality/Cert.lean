/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Engine

import Mathlib.NumberTheory.LucasPrimality

/-!
# Primality certificates from factorisations of `p - 1`

This file proves `Nat.Prime p` for a numeral `p` from a witness `a` and the prime factors of
`p - 1`, by the Lucas test, and finds such certificates with a factor engine.
-/

public section

namespace Mathlib.Tactic.Primality

/-- `LucasHelper p a n` says that `a ^ ((p - 1) / q) % p ≠ 1` for every prime factor `q` of
`n`. -/
inductive LucasHelper (p a : ℕ) : ℕ → Prop
  | one : LucasHelper p a 1
  | cons {m n q e : ℕ} (hq : q.Prime) (hpow : Nat.powMod a ((p - 1) / q) p ≠ 1)
      (hn : q ^ e * m = n) (h : LucasHelper p a m) : LucasHelper p a n

theorem LucasHelper.powMod_ne_one {p a n : ℕ} (h : LucasHelper p a n) {q : ℕ} (hq : q.Prime)
    (hqn : q ∣ n) : Nat.powMod a ((p - 1) / q) p ≠ 1 := by
  induction h with
  | one => exact absurd hqn hq.not_dvd_one
  | @cons m n r e hr hpow hn h ih =>
    obtain hqr | hqm := hq.dvd_mul.mp (hn ▸ hqn)
    · rwa [(Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hqr)]
    · exact ih hqm

theorem LucasHelper.prime {p a : ℕ} (h : LucasHelper p a (p - 1))
    (ha : Nat.powMod a (p - 1) p = 1) : p.Prime := by
  have hp : p ≠ 1 := by
    rintro rfl
    simp [Nat.powMod_def] at ha
  refine lucas_primality p a ?_ fun q hq hqp h1 ↦ h.powMod_ne_one hq hqp ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← Nat.powMod_def, ha, Nat.cast_one]
  · rw [Nat.powMod_def, ← ZMod.val_natCast, Nat.cast_pow, h1, ZMod.val_one'' hp]

end Mathlib.Tactic.Primality

end

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- A certificate for the primality of one number, referring to the primes it depends on by
value. -/
inductive Cert where
  /-- `p` is proved prime by `norm_num`'s evaluation of `Nat.minFac p`. -/
  | minFac (p : Nat)
  /-- `p` is proved prime from the witness `a` and the prime factors `qs` of `p - 1`. -/
  | factors (p a : Nat) (qs : List Nat)

/-- The number that the certificate `c` proves prime. -/
def Cert.subject (c : Cert) : Nat :=
  match c with
  | .minFac p | .factors p _ _ => p

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def minFacBound : Nat := 2 ^ 18

/-- The largest witness tried. -/
def witnessBound : Nat := 1000

/-- Decides whether `n` is prime below `minFacBound`, and runs the base-3 Fermat test above it
(base `2` passes every composite `2 ^ q - 1` with `q` prime). -/
def isProbablePrime (n : Nat) : Bool :=
  if n < minFacBound then decide n.Prime else Nat.powMod 3 (n - 1) n == 1

/-- The least `a` in `[2, witnessBound]` with `a ^ (p - 1) % p = 1` and
`a ^ ((p - 1) / q) % p ≠ 1` for each `q ∈ qs`. -/
def findWitness? (p : Nat) (qs : List Nat) : Option Nat :=
  (2...=witnessBound).iter.find? fun a ↦
    qs.all (fun q ↦ Nat.powMod a ((p - 1) / q) p != 1) && Nat.powMod a (p - 1) p == 1

/-- Appends certificates for `p` and for the primes it depends on that `certs` does not cover yet,
each after the certificates it uses. -/
partial def findCerts (engine : FactorEngine) (p : Nat) : StateT (Array Cert) CoreM Unit := do
  if (← get).any (·.subject == p) then return
  checkSystem "primality"
  unless isProbablePrime p do
    throwError "{p} is not prime"
  if p < minFacBound then
    modify (·.push (.minFac p))
    return
  let (qs, rest) ← factorWith engine (p - 1)
  let qs ←
    if rest == 1 then pure qs
    else if isProbablePrime rest then pure (rest :: qs)
    else throwError "found no prime factor of {rest}, which divides {p} - 1"
  let some a := findWitness? p qs |
    throwError "found no witness for the primality of {p} up to {witnessBound}; \
      it may not be prime"
  for q in qs do
    findCerts engine q
  modify (·.push (.factors p a qs))

/-- Proves `Nat.Prime pQ` for the raw literal `pQ` by `norm_num`'s `Nat.Prime` extension. -/
def certifyMinFac (pQ : Q(Nat)) : MetaM Q(Nat.Prime $pQ) := do
  let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $pQ) | failure
  return pf

/-- Proves `LucasHelper p a n` for the product `n` of the powers of `qs` in `p - 1`, given the
proofs that each `q ∈ qs` is prime. -/
def certifyLucasHelper (proofs : Std.HashMap Nat ((qQ : Q(Nat)) × Q(Nat.Prime $qQ))) (p : Nat)
    (pQ aQ : Q(Nat)) (qs : List Nat) :
    MetaM (Nat × (nQ : Q(Nat)) × Q(LucasHelper $pQ $aQ $nQ)) := do
  match qs with
  | [] => return ⟨1, q(1), q(.one)⟩
  | q :: qs =>
    let ⟨m, mQ, h⟩ ← certifyLucasHelper proofs p pQ aQ qs
    let some ⟨qQ, hq⟩ := proofs[q]? | failure
    let e := (Nat.maxPowDvdDiv q (p - 1)).1
    let n := q ^ e * m
    have eQ : Q(Nat) := mkRawNatLit e
    have nQ : Q(Nat) := mkRawNatLit n
    have hd : Q(Nat.beq (Nat.powMod $aQ (($pQ - 1) / $qQ) $pQ) 1 = false) :=
      (q(Eq.refl false) : Expr)
    have hn : Q($qQ ^ $eQ * $mQ = $nQ) := (q(Eq.refl $nQ) : Expr)
    return ⟨n, nQ, q(LucasHelper.cons $hq (Nat.ne_of_beq_eq_false $hd) $hn $h)⟩

/-- Proves `Nat.Prime p` for the raw literal `p` from the witness `a` and the prime factors `qs` of
`p - 1`, given the proofs that each `q ∈ qs` is prime. -/
def certifyFactors (proofs : Std.HashMap Nat ((qQ : Q(Nat)) × Q(Nat.Prime $qQ))) (p a : Nat)
    (pQ : Q(Nat)) (qs : List Nat) : MetaM Q(Nat.Prime $pQ) := do
  have aQ : Q(Nat) := mkRawNatLit a
  let ⟨n, nQ, h⟩ ← certifyLucasHelper proofs p pQ aQ qs
  unless n == p - 1 do
    throwError "the factors {qs} do not make up {p} - 1"
  have : $nQ =Q $pQ - 1 := ⟨⟩
  have ha : Q(Nat.powMod $aQ ($pQ - 1) $pQ = 1) := (q(Eq.refl 1) : Expr)
  return q(LucasHelper.prime $h $ha)

/-- Proves the certificates `certs` in order, returning each proof under the number it proves
prime. -/
def certify (certs : Array Cert) : MetaM (Std.HashMap Nat ((pQ : Q(Nat)) × Q(Nat.Prime $pQ))) :=
  certs.foldlM (init := {}) fun proofs c ↦ do
    have pQ : Q(Nat) := mkRawNatLit c.subject
    let pf : Q(Nat.Prime $pQ) ← match c with
      | .minFac _ => certifyMinFac pQ
      | .factors p a qs => certifyFactors proofs p a pQ qs
    return proofs.insert c.subject ⟨pQ, pf⟩

end Mathlib.Tactic.Primality
