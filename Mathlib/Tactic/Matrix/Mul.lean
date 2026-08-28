/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Matrix.ListMatrix
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Core

/-!
# `norm_matmul`: products of matrix literals

This module defines the `norm_matmul` simproc, which rewrites a product of matrix literals to
the literal of the product through `Matrix.ofLists_mul`, with the entries computed by
`norm_num`.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.normMatMul

namespace Mathlib.Tactic.Matrix

/-- A finisher rewrites a scalar expression to a normal form. -/
abbrev Finisher := Expr → MetaM Simp.Result

/-- Build `a₀ * b₀ + (a₁ * b₁ + (… + 0))`, the unfolding of `List.dotProduct`. -/
def mkDotProduct {u : Level} {α : Q(Type u)} (_inst : Q(NonUnitalNonAssocSemiring $α))
    (as bs : Array Q($α)) : Q($α) :=
  (as.zipWith (bs := bs) fun (a b : Q($α)) => q($a * $b)).foldr
    (fun (t acc : Q($α)) => q($t + $acc)) q(0)

/-- Prove `[a₀, …] = [b₀, …]` from proofs of `aᵢ = bᵢ`. -/
def mkListCongr (α : Expr) (hs : Array Expr) : MetaM Expr := do
  let u ← getDecLevel α
  hs.foldrM (init := ← mkEqRefl (mkApp (mkConst ``List.nil [u]) α)) fun h acc => do
    mkCongr (← mkCongrArg (mkApp (mkConst ``List.cons [u]) α) h) acc

/-- Prove `e = C`, where `e` is the product of the matrix literals with rows `rowsA` and
`rowsB` over `R`, and `C` is the literal of the product with entries normalized by `finish`. -/
def proveMul (finish : Finisher) (e : Expr) (l m n : ℕ) (R : Expr)
    (rowsA rowsB : Array (Array Expr)) : MetaM Simp.Result := do
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let _inst ← synthInstanceQ q(NonUnitalNonAssocSemiring $α)
  let cols : Array (Array Expr) :=
    Array.ofFn (n := n) fun j => Array.ofFn (n := m) fun i => (rowsB[i]!)[j]!
  let results ← Array.ofFnM (n := l) fun i => Array.ofFnM (n := n) fun j => do
    let r ← finish (mkDotProduct (α := α) _inst rowsA[i]! cols[j]!)
    return (r.expr, ← r.getProof)
  let entries := results.map (·.map (·.1))
  let hAll ← mkListCongr q(List $α) (← results.mapM fun row => mkListCongr α (row.map (·.2)))
  let mkLists (rows : Array (Array Expr)) : MetaM Q(List (List $α)) := do
    mkListLit q(List $α) (← rows.toList.mapM (mkListLit α ·.toList))
  have A : Q(List (List $α)) := ← mkLists rowsA
  have B : Q(List (List $α)) := ← mkLists rowsB
  let C : Q(Matrix (Fin $l) (Fin $n) $α) :=
    Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (entries[i]!)[j]!)
  let hmul := q((Matrix.ofLists_mul $l $m $n $A $B).symm)
  let hC ← mkCongrArg q(Matrix.ofLists (α := $α) $l $n) hAll
  let pf ← mkEqTrans hmul hC
  return { expr := C, proof? := some (← mkExpectedTypeHint pf (← mkEq e C)) }

/-- Core of the `norm_matmul` simproc with the given finisher. The factors are simplified first,
so that a product of products is evaluated inside-out before the simp lemmas on `vecCons`
products apply. -/
def normMatMulCore (finish : Finisher) : Simp.Simproc := fun e => do
  let_expr HMul.hMul _ _ _ _ A B := e | return .continue
  let rA ← Simp.simp A
  let rB ← Simp.simp B
  let some (l, m, R, rowsA) ← matchMatrixLit? rA.expr
    | trace[Tactic.normMatMul] "not a closed matrix literal{indentExpr rA.expr}"
      return .continue
  let some (_, n, _, rowsB) ← matchMatrixLit? rB.expr
    | trace[Tactic.normMatMul] "not a closed matrix literal{indentExpr rB.expr}"
      return .continue
  let rAB ← Simp.mkCongr (← Simp.mkCongr { expr := e.appFn!.appFn! } rA) rB
  return .visit (← rAB.mkEqTrans (← proveMul finish rAB.expr l m n R rowsA rowsB))

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Use it as
`simp [↓ norm_matmul]`: as a pre-procedure it takes precedence over the simp lemmas unfolding
products of `vecCons` rows, and `norm_num` ignores simprocs given as arguments. Terms that it
cannot evaluate are skipped, and can be viewed by using `set_option trace.Tactic.normMatMul true`.
-/
simproc_decl norm_matmul (_ * _) := fun e => do
  try normMatMulCore (Mathlib.Meta.NormNum.eval ·) e
  catch ex =>
    trace[Tactic.normMatMul] "{ex.toMessageData}"
    return .continue
