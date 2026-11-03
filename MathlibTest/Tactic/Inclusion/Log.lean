/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

-- The bounds on `log 2` and `log 3` of `Mathlib.Analysis.Complex.ExponentialBounds`.
example : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 := by
  dyadic_interval [prec := 33]

example : 1.0986122885 < Real.log 3 ∧ Real.log 3 < 1.0986122888 := by
  dyadic_interval [prec := 34]

example : 0.094 < Real.log (Real.log 3) ∧ Real.log (Real.log 3) < 0.0941 := by
  dyadic_interval [prec := 16]

example {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.log x := by dyadic_interval

example : 0.69 < Real.log (-2) := by dyadic_interval [prec := 10]

example : Real.log 0 = 0 := by dyadic_interval

example {x : ℝ} (h₁ : -1 ≤ x) (h₂ : x ≤ 1) : Real.log x ≤ 0 := by dyadic_interval

/-- error: The inclusion check failed:
The proposition was not proven true or false. -/
#guard_msgs in
example {x : ℝ} (hx : x ≤ 1) (h : False) : Real.log x ≤ 0 := by
  dyadic_interval?
  exact h.elim

end Inclusion.Tests
