/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Init

/-!
# Producers

This file defines the producers of the witnesses of primality certificates. Factorizers find prime
factors of `p - 1`, and primitive root finders find primitive roots of `p`.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

section Factorizer

/-- Returns distinct prime factors of the input, not necessarily all of them. The factorizer must
ensure that they are prime. It works in `CoreM` to check heartbeats and handle cancellation. -/
abbrev Factorizer := Nat → CoreM (Array Nat)

/-- Returns the prime factors of `n` that `f` finds, and `n` with all of them divided out. -/
def Factorizer.decompose (f : Factorizer) (n : Nat) : CoreM (Array Nat × Nat) := do
  let ps ← f n
  return (ps, ps.foldl Nat.divMaxPow n)

/-- Returns the candidates in `ps` that divide its input. They are assumed prime, and each is
divided out completely, so a repeated candidate is returned once. -/
def Factorizer.ofArray (ps : Array Nat) : Factorizer := fun n ↦
  pure (ps.foldl (init := (#[], n)) fun (found, rest) p ↦
    if 1 < p && rest % p == 0 then (found.push p, rest.divMaxPow p) else (found, rest)).1

/-- Runs `f₁` on `n`, then `f₂` on what is left after dividing out the factors `f₁` returned. -/
def Factorizer.then (f₁ f₂ : Factorizer) : Factorizer := fun n ↦ do
  let (ps, rest) ← f₁.decompose n
  return ps ++ (← f₂ rest)

/-- Trial division by `2` and the odd numbers up to `bound`. A remaining factor that trial division
shows to be prime is returned as well. -/
def trialDivision (bound : Nat) : Factorizer := fun n ↦ do
  let mut n := n
  let mut ps := #[]
  let mut k := 2
  while k ≤ bound && k * k ≤ n do
    if n % k == 0 then
      ps := ps.push k
      n := n.divMaxPow k
    if k % 4096 == 1 then
      checkSystem "trialDivision"
    k := if k == 2 then 3 else k + 2
  if 1 < n && n < k * k then
    ps := ps.push n
  return ps

section PollardRho

/-- Whether `n` passes the Miller–Rabin test to the prime bases up to `41`, which no composite below
`3.3 * 10 ^ 24` does. -/
def isProbablePrime (n : Nat) : Bool := Id.run do
  let bases := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  if n < 2 then return false
  if let some a := bases.find? (n % · == 0) then return n == a
  let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
  for a in bases do
    let mut x := Nat.powMod a d n
    if x == 1 then continue
    for _ in 1...s do
      if x == n - 1 then break
      x := x * x % n
    if x != n - 1 then return false
  return true

/-- Finds a factor of `n` other than `1` and `n` by Pollard's rho method with `x ↦ x ^ 2 + c`,
trying `c = 1, 2, 3` for at most `steps` steps each. -/
def rhoFactor? (n steps : Nat) : CoreM (Option Nat) := do
  for c in 1...=3 do
    let mut x := 2
    let mut y := 2
    for i in 0...steps do
      if i % 4096 == 0 then
        checkSystem "pollardRho"
      x := (x * x + c) % n
      y := (y * y + c) % n
      y := (y * y + c) % n
      let d := Nat.gcd (x + n - y) n
      if d == n then break
      if d != 1 then return some d
  return none

/-- Splits `n` by `rhoFactor?` into factors that pass `isProbablePrime`, and returns the distinct
ones. A part that it cannot split is left out. -/
partial def pollardRho (steps : Nat) : Factorizer := fun n ↦ do
  if n < 2 then return #[]
  if isProbablePrime n then return #[n]
  let some d ← rhoFactor? n steps | return #[]
  let ps ← pollardRho steps d
  return ps ++ (← pollardRho steps (n / d)).filter (!ps.contains ·)

end PollardRho

/-- Options for factorizing `p - 1`. -/
structure FactorizerConfig where
  /-- Candidate prime factors, tried before trial division on `p - 1` and on `q - 1` for each prime
  `q` proved on the way. They must be prime. -/
  factors : List Nat := []
  /-- The number of steps of Pollard's rho method for each constant it tries. The default finds
  prime factors below `10 ^ 8`. -/
  rhoSteps : Nat := 2 ^ 15

/-- Tries `factors`, then trial division up to `1024`, then Pollard's rho method. -/
def FactorizerConfig.toFactorizer (cfg : FactorizerConfig) : Factorizer :=
  Factorizer.then (.ofArray cfg.factors.toArray) <|
    (trialDivision 1024).then (pollardRho cfg.rhoSteps)

end Factorizer

section PrimitiveRootFinder

/-- Given the prime factors `qs` of `p - 1`, returns a primitive root of `p` or a Fermat witness. -/
abbrev PrimitiveRootFinder := Nat → Array Nat → CoreM (Option Nat)

/-- Tries the candidates `roots` in order, each reduced modulo `p`. -/
def PrimitiveRootFinder.ofArray (roots : Array Nat) : PrimitiveRootFinder := fun p qs ↦ do
  for a in roots do
    let a := a % p
    if a != 0 && (Nat.powMod a (p - 1) p != 1 ||
        qs.all fun q ↦ Nat.powMod a ((p - 1) / q) p != 1) then
      return some a
  return none

/-- Runs `f₁`, followed by `f₂` if `f₁` finds nothing. -/
def PrimitiveRootFinder.then (f₁ f₂ : PrimitiveRootFinder) : PrimitiveRootFinder := fun p qs ↦ do
  if let some a ← f₁ p qs then
    return some a
  f₂ p qs

/-- Tries `2, …, bound - 1` as primitive roots. -/
def trialRoots (bound : Nat) : PrimitiveRootFinder :=
  .ofArray (Array.range' 2 (bound - 2))

/-- Options for finding primitive roots. -/
structure PrimitiveRootFinderConfig where
  /-- Candidate primitive roots, tried before the search. -/
  roots : List Nat := []
  /-- Primitive roots are tried below this bound. -/
  primitiveRootBound : Nat := 1024

/-- Tries `roots`, then the numbers below `primitiveRootBound`. -/
def PrimitiveRootFinderConfig.toRootFinder (cfg : PrimitiveRootFinderConfig) :
    PrimitiveRootFinder :=
  .then (.ofArray cfg.roots.toArray) (trialRoots cfg.primitiveRootBound)

end PrimitiveRootFinder

end Mathlib.Tactic.Primality
