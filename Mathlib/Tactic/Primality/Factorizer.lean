/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Init

/-!
# Factorizers

This file defines the interface of factorizers, which find prime factors for primality
certificates, and trial division up to a given bound.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

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

end Mathlib.Tactic.Primality
