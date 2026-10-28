module

import Mathlib.Tactic.Primality

/-! # Tests for the `primality` tactic -/

/-- error: the goal is not of the form `Nat.Prime n` -/
#guard_msgs in
example : 2 = 2 := by primality

/-- error: n does not evaluate to a numeral -/
#guard_msgs in
example (n : ℕ) : Nat.Prime n := by primality

/-! The goal's type is a metavariable assigned by `refine`. -/

example : ∃ p, Nat.Prime p ∧ p = 7 := by
  refine ⟨_, ?_, rfl⟩
  primality

/-! `p - 1 = 2 ^ 10 * 3 * 7 * 13`. -/

example : Nat.Prime 279553 := by primality

/-! Trial division leaves one large factor in each of the first three `n - 1` below, and that
factor is proved prime in turn. It factors the last two completely.
* `4398046517687 - 1 = 2 * 2199023258843`
* `2199023258843 - 1 = 2 * 1099511629421`
* `1099511629421 - 1 = 2 ^ 2 * 5 * 251 * 219026221`
* `219026221 - 1 = 2 ^ 2 * 3 * 5 * 7 * 521491`
* `521491 - 1 = 2 * 3 * 5 * 17383` -/

example : Nat.Prime 4398046517687 := by primality

/-- error: primality could not determine whether these numbers, needed to certify 8798165024603,
are prime: [4399082512301]. For each of them, add a prime factor of it to `factors` if it is not
prime, or a primitive root of it to `roots` if it is prime. -/
#guard_msgs in
example : Nat.Prime 8798165024603 := by primality

/-! The hint `2097169` splits `p - 1 = 2 * 2097169 * 2097629`, whose odd prime factors are both
beyond the trial division. -/

example : Nat.Prime 8798165024603 := by primality (factors := [2097169])
