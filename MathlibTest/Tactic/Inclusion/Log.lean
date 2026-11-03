/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

open Real

-- The bounds on `log 2` and `log 3` of `Mathlib.Analysis.Complex.ExponentialBounds`.
example : 0.6931471803 < log 2 ∧ log 2 < 0.6931471808 := by
  dyadic_interval [prec := 33]

example : 1.0986122885 < log 3 ∧ log 3 < 1.0986122888 := by
  dyadic_interval [prec := 34]

example : 0.094 < log (log 3) ∧ log (log 3) < 0.0941 := by
  dyadic_interval [prec := 16]

example : 1.098612288668109691395245236922 < log 3 ∧ log 3 < 1.098612288668109691395245236923 := by
  dyadic_interval [prec := 102]

example {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log x := by dyadic_interval

example : 0.69 < log (-2) := by dyadic_interval [prec := 10]

example : log 0 = 0 := by dyadic_interval

example : log (-1) = 0 := by dyadic_interval

example : log 1 = 0 := by dyadic_interval

example {x : ℝ} (h₁ : -1 ≤ x) (h₂ : x ≤ 1) : log x ≤ 0 := by dyadic_interval

/-- error: The inclusion check failed:
The proposition was not proven true or false. -/
#guard_msgs in
example {x : ℝ} (hx : x ≤ 1) (h : False) : log x ≤ 0 := by
  dyadic_interval?
  exact h.elim

end Inclusion.Tests
