/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.SinCos

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : 0.8414709848 < Real.sin 1 := by dyadic_interval [prec := 37]

example {x : ℝ} (h₁ : 1.5 ≤ x) (h₂ : x ≤ 1.6) : 0.9 < Real.sin x ∧ Real.sin x ≤ 1 := by
  dyadic_interval [prec := 6]

example {x : ℝ} (h₁ : 4 ≤ x) (h₂ : x ≤ 5) : Real.sin x < -0.75 := by
  dyadic_interval [prec := 7]

example {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 3.5) : -0.36 < Real.sin x := by
  dyadic_interval [prec := 6]

example {x : ℝ} (h₁ : 1.65 ≤ x) (h₂ : x ≤ 7.75) : Real.sin x < 0.998 := by
  dyadic_interval [prec := 12]

example {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 8) : Real.sin x ≤ 1 := by dyadic_interval

example (x : ℝ) : Real.sin x ≤ 1 := by dyadic_interval

example {x : ℝ} (h₁ : 3 ≤ x) (h₂ : x ≤ 3.3) : Real.cos x < -0.98 := by
  dyadic_interval [prec := 9]

end Inclusion.Tests
