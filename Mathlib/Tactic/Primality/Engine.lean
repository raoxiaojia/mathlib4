/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Init

/-!
# Prime factor finding engines

This file defines the interface of the engines that find prime factors for primality
certificates, and trial division as the default engine.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

/-- A prime factor finding engine. It returns distinct factors of `n` that it takes to be prime
(`[]` when it finds none), not necessarily all of them. -/
abbrev FactorEngine := Nat → CoreM (List Nat)

/-- Divides out of `n` every prime factor that `engine` finds, returning the primes found and the
cofactor left. -/
def factorWith (engine : FactorEngine) (n : Nat) : CoreM (List Nat × Nat) := do
  let qs ← engine n
  let mut rest := n
  for q in qs do
    unless 1 < q && rest % q == 0 do
      throwError "the factor engine returned {q}, which is not a new factor of {n}"
    rest := rest.divMaxPow q
  return (qs, rest)

/-- Trial division of `n` by the numbers in `qs`, in order, returning those that divide what the
earlier ones left. They are candidates supplied by the user, so their primality is checked when
they are certified. -/
def FactorEngine.ofList (qs : List Nat) (n : Nat) : CoreM (List Nat) :=
  pure (qs.foldl (init := ([], n)) fun (found, rest) q ↦
    if 1 < q && rest % q == 0 then (found ++ [q], rest.divMaxPow q) else (found, rest)).1

/-- Runs `e₁` on `n`, then `e₂` on what is left after dividing out the factors `e₁` returned. -/
def FactorEngine.andThen (e₁ e₂ : FactorEngine) (n : Nat) : CoreM (List Nat) := do
  let (qs, rest) ← factorWith e₁ n
  return qs ++ (← e₂ rest)

/-- Trial division of `n` by `2` and the odd numbers up to `bound`. Besides the prime factors it
divides out, it returns the cofactor left over when it is prime because it is below the square of
the next trial divisor. It stops early once the cofactor exceeds `bound ^ 2` and passes the base-3
Fermat test, leaving the cofactor to the caller. -/
def trialDivision (bound n : Nat) : CoreM (List Nat) := do
  let mut n := n
  let mut qs := #[]
  let mut k := 2
  while k ≤ bound && k * k ≤ n do
    if n % k == 0 then
      qs := qs.push k
      n := n.divMaxPow k
      if bound * bound < n && Nat.powMod 3 (n - 1) n == 1 then
        break
    if k % 4096 == 1 then
      checkSystem "trialDivision"
    k := if k == 2 then 3 else k + 2
  if 1 < n && n < k * k then
    qs := qs.push n
  return qs.toList

end Mathlib.Tactic.Primality
