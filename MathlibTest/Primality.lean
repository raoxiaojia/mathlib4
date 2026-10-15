module

import Mathlib.Tactic.Primality

import Mathlib.Algebra.Ring.Rat

-- single primes as the first and a later factor, certified by `small`
example : Nat.Prime 31 := by prime_cert [small {2; 3}, pock (31, 3, 2 * 3)]

-- a prime power as a later factor; the factors 2 and 3 are proved on demand
example : Nat.Prime 73 := by prime_cert [pock (73, 5, 3 * 2 ^ 3)]

-- a prime power as the first factor, and a prime certified by `pock` reused as a factor
example : Nat.Prime 16290860017 := by
  prime_cert [pock {(339392917, 2, 3 ^ 4 * 29 * 41); (16290860017, 5, 339392917)}]

-- a factor above the on-demand bound must be certified by an earlier step
/-- error: Primality not yet certified for 339392917 -/
#guard_msgs in
example : Nat.Prime 16290860017 := by prime_cert [pock (16290860017, 5, 339392917)]

-- `small` rejects a composite number
/-- error: prime_cert: 4 is not prime -/
#guard_msgs in
example : Nat.Prime 31 := by prime_cert [small {4}]

-- the term elaborator
example : Nat.Prime 31 := prime_cert% [pock (31, 3, 2 * 3)]

-- general `Prime` goal (bridged via `Nat.Prime.prime`)
example : Prime 31 := by prime_cert [small {31}]

-- nested conjunction
example : Nat.Prime 2 ∧ Nat.Prime 3 ∧ Prime 31 := by prime_cert [small {2; 3; 31}]

-- a non-ℕ `Prime` goal is rejected cleanly, not passed off to the kernel
/-- error: prime_cert: the general `Prime` goal is only supported over ℕ, not ℚ -/
#guard_msgs in
example : Prime (3 : ℚ) := by prime_cert [small {3}]
