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

This file defines the interface of the factorizers that find prime factors for primality
certificates, and a default factorizer by trial division up to a given bound.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

/-- Returns an array of distinct prime factors of the input that the factorizer can find. This does
not have to be complete (e.g. the factorizer can return an empty array for numbers that are too
difficult to factor). It is the factorizer's obligation to ensure that all values it returned are
indeed prime.

Works in `CoreM` so the factorizer can check for heartbeats consumed and handle
cancellation. -/
abbrev Factorizer := Nat → CoreM (Array Nat)

/-- Divides out of `n` every prime factor that the factorizer finds, and returns the prime factors
found and the remaining factor. -/
def Factorizer.decompose (f : Factorizer) (n : Nat) : CoreM (Array Nat × Nat) := do
  let ps ← f n
  let mut ret := n
  for p in ps do
    ret := ret.divMaxPow p
  return (ps, ret)

/-- Assembles a factorizer based on an array of prime candidates based on trial division. This is
for handling candidate prime factors that user provides in the certificate witness. -/
def Factorizer.ofArray (ps : Array Nat) : Factorizer := fun n ↦
  pure (ps.foldl (init := (#[], n)) fun (found, rest) p ↦
    if 1 < p && rest % p == 0 then (found.push p, rest.divMaxPow p) else (found, rest)).1

/-- Runs `f₁` on `n`, then `f₂` on what is left after dividing out the factors `f₁` returned. -/
def Factorizer.then (f₁ f₂ : Factorizer) : Factorizer := fun n ↦ do
  let (ps, rest) ← f₁.decompose n
  return ps ++ (← f₂ rest)

/-- Trial division by `2` and the odd numbers up to `bound` and returns all prime factors found. -/
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
