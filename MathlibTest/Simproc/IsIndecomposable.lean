import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.Simproc.IsIndecomposable

open Matrix CartanMatrix

/-! ## Literals over `ℤ` -/

example : (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- no edge from `0` to `1`, so the search from `0` fails
example : ¬(!![2, 0; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

-- no edge from `1` to `0`, so the search from `0` succeeds and the search back to `0` fails
example : ¬(!![2, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

example : (!![5] : Matrix (Fin 1) (Fin 1) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (0 : Matrix (Fin 0) (Fin 0) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

example : ¬(!![1, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

/-! ## Matrices given by functions or constants -/

example : (A 8).IsIndecomposable := by simp only [reduceIsIndecomposable]
example : (B 5).IsIndecomposable := by simp only [reduceIsIndecomposable]
example : (C 5).IsIndecomposable := by simp only [reduceIsIndecomposable]
example : (D 6).IsIndecomposable := by simp only [reduceIsIndecomposable]
example : (E 8).IsIndecomposable := by simp only [reduceIsIndecomposable]
example : F₄.IsIndecomposable := by simp only [reduceIsIndecomposable]
example : G₂.IsIndecomposable := by simp only [reduceIsIndecomposable]

example : ¬(D 2).IsIndecomposable := by
  simp [reduceIsIndecomposable]

-- no edge from `7` to `8`
example : ¬(Matrix.of fun i j : Fin 16 ↦ if i = j then (2 : ℤ)
    else if i.val + 1 = j.val ∧ i.val ≠ 7 then -1 else if j.val + 1 = i.val then -1 else 0
    ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

-- no edge from `8` to `7`
example : ¬(Matrix.of fun i j : Fin 16 ↦ if i = j then (2 : ℤ)
    else if i.val + 1 = j.val then -1 else if j.val + 1 = i.val ∧ i.val ≠ 8 then -1 else 0
    ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

/-! ## Other entry types -/

example : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℕ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (!![1/2, 1/3; 1/5, 0] : Matrix (Fin 2) (Fin 2) ℚ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

/-! ## Terms the simproc skips -/

-- equality on `ℝ` is classical, so the kernel cannot decide it
/--
error: `simp` made no progress
---
trace: [Tactic.reduceIsIndecomposable] the kernel cannot decide which entries are zero
      !![1, 2; 3, 4]
-/
#guard_msgs in
set_option trace.Tactic.reduceIsIndecomposable true in
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

/--
error: `simp` made no progress
---
trace: [Tactic.reduceIsIndecomposable] the matrix is not closed
      !![x, 1; 1, 0]
-/
#guard_msgs in
set_option trace.Tactic.reduceIsIndecomposable true in
example (x : ℤ) : (!![x, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

/--
error: `simp` made no progress
---
trace: [Tactic.reduceIsIndecomposable] the index type is not `Fin n`
      Fin 1 ⊕ Fin 1
-/
#guard_msgs in
set_option trace.Tactic.reduceIsIndecomposable true in
example : (fromBlocks !![1] !![1] !![1] !![1] :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]
