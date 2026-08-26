/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss

/-!
# `eval_rank`: rank of matrix literals by Bareiss elimination

This module defines the `eval_rank` tactic and the `norm_rank` simproc, which compute
the rank of a matrix literal with non-symbolic entries through an
`Echelon.Decomposition` certificate checked by the kernel.
-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic.Echelon

/-- Rewrite `Matrix.rank A` to the pivot count of the decomposition certificate of the
matrix literal `A`; `none` when no certificate is produced. -/
def normalizeRank (e A : Expr) : MetaM (Option Simp.Result) := do
  let some res ← mkBareissDecomposition? A | return none
  let pf ← mkAppM ``Echelon.Decomposition.rank_eq #[res.cert]
  let k := mkNatLit res.data.pivot.size
  return some { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }

/-- Core of the `norm_rank` simproc. -/
def normRankCore : Simp.Simproc := fun e => do
  let_expr Matrix.rank _ _ _ _ _ A := e | return .continue
  let some r ← normalizeRank e A | return .continue
  return .done r

end Mathlib.Tactic.Echelon

open Mathlib.Tactic.Echelon

/-- The `norm_rank` simproc evaluates the rank of matrices with non-symbolic entries.
Terms that it cannot evaluate are skipped. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  try normRankCore e
  catch ex =>
    trace[Tactic.evalRank] "{ex.toMessageData}"
    return .continue

/--
`eval_rank` evaluates the rank of matrices with non-symbolic entries.

The element type must be a commutative domain with kernel-decidable equality against
zero, or of characteristic zero.
Terms skipped can be viewed by using `set_option trace.Tactic.evalRank true`.
-/
elab (name := evalRank) "eval_rank" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_rank]))
  catch _ =>
    throwError "`eval_rank` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalRank true`."
  Tactic.evalTactic (← `(tactic| try lia))
