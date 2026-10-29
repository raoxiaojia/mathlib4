module

import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic.Primality

/-! # Tests for the `primality` tactic -/

/-! ## Lucas certificates

Proves `Nat.Prime p` by the Lucas test from a primitive root and certified prime factors of `p - 1`,
with each of the intermediate primes proved the same way with the same factor hints, unless the user
provides proofs.
-/

example : Nat.Prime 100000007 := by primality

example : Nat.Prime (10 ^ 9 + 7) := by simp; primality

/-- error: primality could not find factors for these intermediate values:
[100000000004900000000016761]; factors can be provided at `.lucas { factors := … }`. In the rare
case that any of the values is prime, add primitive roots of them to `.lucas { roots := … }`. -/
#guard_msgs in
example : Nat.Prime (2 * 10000000000037 * 10000000000453 + 1) := by primality

example : Nat.Prime (2 * 10000000000037 * 10000000000453 + 1) := by
  simp; primality (cert := .lucas { factors := [10000000000037] })

example : Nat.Prime (2 * 1000021069 * 100000000000031 + 1) := by
  primality (cert := .lucas { rhoSteps := 2 ^ 16 })

theorem prime_4398046517687 : Nat.Prime 4398046517687 := by primality

-- Takes an already proven prime as a hint.
example : Nat.Prime (2 * 4398046517687 * 10000000001437 + 1) := by
  primality (cert := .lucas { proofs := [prime_4398046517687] })

-- The same with a hypothesis.
example (h : Nat.Prime 4398046517687) : Nat.Prime (2 * 4398046517687 * 10000000001437 + 1) := by
  primality (cert := .lucas { proofs := [h] })

/-! ## Special primes -/

example : Nat.Prime (2 ^ 61 - 1) := by simp; primality

-- Only the last 3 factors are required, but 5 are included so the cert checks faster.
set_option exponentiation.threshold 521 in
example : Nat.Prime (2 ^ 521 - 1) := by
  simp
  primality (cert := .lucas { factors := [308761441, 2400573761, 65427463921, 108140989558681,
    145295143558111] })

open Nat in
example : Nat.Prime (73 ! + 1) := by simp [Nat.factorial]; primality

/-! ## Errors -/

/-- error: n does not evaluate to a numeral; try simplifying it first -/
#guard_msgs in
example (n : ℕ) : Nat.Prime n := by primality

/-- error: primality is unable to find a primitive root for 1000001; primitive roots can be
provided at `.lucas { roots := … }` if 1000001 is prime. -/
#guard_msgs in
example : Nat.Prime 1000001 := by primality
