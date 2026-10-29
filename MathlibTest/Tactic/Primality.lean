module

import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic.Primality

/-! # Tests for the `primality` tactic -/

/-! ## Lucas certificates -/

example : Nat.Prime 100000007 := by primality

example : Nat.Prime (10 ^ 9 + 7) := by simp; primality

/-- error: primality could not find factors for these intermediate values: [4399082512301]; factors
can be explicitly provided at `.lucas { factors := … }`. In the rare case that any of the values is
prime, add primitive roots of them to `.lucas { roots := … }`. -/
#guard_msgs in
example : Nat.Prime 8798165024603 := by primality

-- `p - 1 = 2 * 2097169 * 2097629`, and trial division finds neither odd factor.
example : Nat.Prime 8798165024603 := by primality (cert := .lucas { factors := [2097169] })

-- `2130047 - 1 = 2 * 1031 * 1033`, whose odd prime factors are both beyond the default bound.
example : Nat.Prime 2130047 := by primality (cert := .lucas { trialDivisionBound := 1031 })
-- `4398046517687 - 1 = 2 * 2199023258843`
-- `2199023258843 - 1 = 2 * 1099511629421`
-- `1099511629421 - 1 = 2 ^ 2 * 5 * 251 * 219026221`
-- `219026221 - 1 = 2 ^ 2 * 3 * 5 * 7 * 521491`
-- `521491 - 1 = 2 * 3 * 5 * 17383`
theorem prime_4398046517687 : Nat.Prime 4398046517687 := by primality

-- `p - 1 = 2 * 999763 * 4398046517687`, and trial division finds neither odd factor.
example : Nat.Prime 8794008361324616363 := by
  primality (cert := .lucas { proofs := [prime_4398046517687] })

-- The same with a hypothesis.
example (h : Nat.Prime 4398046517687) : Nat.Prime 8794008361324616363 := by
  primality (cert := .lucas { proofs := [h] })

/-! ## Special primes -/

example : Nat.Prime (2 ^ 61 - 1) := by simp; primality

set_option exponentiation.threshold 521 in
example : Nat.Prime (2 ^ 521 - 1) := by
  simp
  primality (cert := .lucas { factors := [1433, 1613, 2731, 3191, 8191, 28793, 42641, 51481,
    61681, 409891, 858001, 5746001, 7623851, 34110701, 308761441, 2400573761, 65427463921,
    108140989558681, 145295143558111] })

open Nat in
example : Nat.Prime (73 ! + 1) := by simp [Nat.factorial]; primality

/-! ## Errors -/

/-- error: n does not evaluate to a numeral; try simplifying it first -/
#guard_msgs in
example (n : ℕ) : Nat.Prime n := by primality

/-- error: primality cannot prove that 1000 is prime: unable to find a primitive root; primitive
roots can be explicitly provided at `.lucas { roots := … }`. -/
#guard_msgs in
example : Nat.Prime 1000 := by primality

-- `2` is a Fermat witness for `1000001 = 101 * 9901`.
/-- error: primality cannot prove that 1000001 is prime: unable to find a primitive root; primitive
roots can be explicitly provided at `.lucas { roots := … }`. -/
#guard_msgs in
example : Nat.Prime 1000001 := by primality
