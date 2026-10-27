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

/-! Below `minFacBound`, composites are rejected exactly. -/

/-- error: 1001 is not prime -/
#guard_msgs in
example : Nat.Prime 1001 := by primality

/-! Above `minFacBound`, `2 ^ 23 - 1 = 47 * 178481` passes the base-2 Fermat test but not the
base-3 one. -/

/-- error: 8388607 is not prime -/
#guard_msgs in
example : Nat.Prime 8388607 := by primality

/-! `p - 1 = 2 ^ 10 * 3 * 7 * 13`, whose cofactor `91 = 7 * 13` passes the base-3 Fermat test but
is below the square of the trial division bound, so trial division does not stop at it. -/

example : Nat.Prime 279553 := by primality

/-! `p - 1 = 2 * 2199023256029`, whose prime cofactor is beyond the trial division and is
certified in turn. -/

example : Nat.Prime 4398046512059 := by primality

/-- error: found no prime factor of 4399082512301, which divides 8798165024603 - 1 -/
#guard_msgs in
example : Nat.Prime 8798165024603 := by primality

/-! The hint `2097169` splits `p - 1 = 2 * 2097169 * 2097629`, whose odd prime factors are both
beyond the trial division. -/

example : Nat.Prime 8798165024603 := by primality (factors := [2097169])

/-! The Carmichael number `278545 = 5 * 17 * 29 * 113` passes the base-3 Fermat test. -/

/-- error: found no witness for the primality of 278545 up to 1000; it may not be prime -/
#guard_msgs in
example : Nat.Prime 278545 := by primality
