/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Echelon.Parsing

/-!
# The Bareiss decomposition driver

Given a matrix literal `A` over a commutative domain, the entry point `mkBareissDecomposition?`
selects a computation model for the element type, runs the elimination, and elaborates a
certificate `Echelon.Decomposition A` through `Mathlib.Tactic.Echelon.Cert`: through a
registered model or the rational model when equality with zero in the element type
reduces in the kernel, and through a certificate over the matrix of the entries' values
transported along the cast homomorphism otherwise, which requires characteristic zero.
The elimination itself is the model-parameterized `bareissDecomp` in
`Mathlib.Tactic.Echelon.Core`.

## Main definitions

- `mkBareissDecomposition?`: the entry point: parse a matrix literal and produce the
  decomposition certificate.
- `mkBareissDecomposition`: select the construction, run the elimination, and elaborate
  the certificate.
- `BareissResult`: the elaborated certificate together with the computed decomposition data.
- `producerFor?`: select a registered computation model for a ring.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.evalRank

namespace Mathlib.Tactic.Echelon

/-- Select a registered computation model for the ring expression `R`: the first
`bareiss_ext` extension that handles `R`. -/
def producerFor? (R : Expr) : MetaM (Option Producer) := do
  for (name, ext) in bareissExt.getState (← getEnv) do
    if let some p ← ext.producer? R then
      trace[Tactic.evalRank] "selected the model `{name}` for{indentExpr R}"
      return some p
  return none

/-- Whether equality with zero in `α` reduces to a verdict in the kernel: for such rings
the certificate conditions are decided by kernel reduction, and otherwise the
certificate is transported from the matrix of the entries' values. -/
def checkKernelDecide {u : Level} (α : Q(Type u)) (cr : Q(CommRing $α)) : MetaM Bool := do
  -- `Decidable` of the single equality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some inst ← synthInstance? q(Decidable (((1 : ℤ) : $α) = 0))
    | return false
  -- check if the equality reduced to a concrete false
  return (Kernel.whnf (← getEnv) (← getLCtx) inst).toOption.any
    (·.isAppOf ``Decidable.isFalse)

/-- The result of producing a decomposition by Bareiss. -/
structure BareissResult where
  /-- The elaborated `Echelon.Decomposition` certificate term. -/
  cert : Expr
  /-- The decomposition data underlying the certificate. -/
  data : BareissData Expr

/-- Produce and elaborate the `Echelon.Decomposition` certificate of the matrix literal
`A`: select the computation model, run the elimination, and build the certificate over
the element type (`mkCertificate`) or over the matrix of the entries' values
(`mkCastCertificate`). -/
def mkBareissDecomposition {u : Level} (A : Expr) (m n : Nat) (α : Q(Type u))
    (entries : Array (Array Expr)) : MetaM BareissResult := do
  have cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  have A : Q(Matrix (Fin $m) (Fin $n) $α) := A
  if let some p ← producerFor? α then
    let d ← p entries
    return { cert := ← mkCertificate cr A d, data := d }
  if ← checkKernelDecide α cr then
    let d ← (← ratProducer α) entries
    return { cert := ← mkCertificate cr A d, data := d }
  let .some cz ← trySynthInstanceQ q(CharZero $α)
    | throwError "equality with zero in the element type is undecidable and the \
        characteristic is not zero{indentExpr A}"
  -- recognize every entry as a rational numeral via `norm_num`, and run the
  -- elimination on the values
  let mut values : Array (Array Rat) := #[]
  let mut nonInt? : Option Expr := none
  for row in entries do
    let mut vrow : Array Rat := #[]
    for entry in row do
      let v ← evalRatEntry true entry
      if v.den != 1 && nonInt?.isNone then
        nonInt? := some entry
      vrow := vrow.push v
    values := values.push vrow
  let (intRows, scales) := scaleRowsIntegral values
  let d := restoreScaling scales (← bareissDecomp (intRingOps 0) intRows)
  let (cert, data) ← match nonInt? with
    | none =>
      mkCastCertificate cr (q(inferInstance) : Q(CommRing ℤ)) q(Int.castRingHom $α)
        q(Int.cast_injective (α := $α))
        (fun v => pure (Meta.NormNum.mkRawIntLit v.num)) A values d
    | some e => do
      -- defensive: a non-integral value arises only from an `isRat` result, which
      -- already requires a `DivisionRing`, so a domain failing `Field` synthesis here
      -- is pathological
      let .some fα ← trySynthInstanceQ q(Field $α)
        | throwError "expected the element type to be a field for the non-integral \
            entry{indentExpr e}{indentExpr A}"
      have _fα : Q(Field $α) := fα
      -- rebound here: the outer pattern-bound `cz` is not harvested as an instance for
      -- the quotations of this nested arm
      have _cz : Q(CharZero $α) := cz
      mkCastCertificate cr (q(inferInstance) : Q(CommRing ℚ)) q(Rat.castHom $α)
        q(Rat.cast_injective (α := $α))
        (fun v => pure (Meta.NormNum.mkRawRatLit v)) A values d
  return { cert, data }

/-- Produce and elaborate the `Echelon.Decomposition` certificate of the matrix literal
`A`. Returns `none`, with the reason traced, when `A` is not a closed matrix literal or
the element type is not a commutative domain; failures of the certificate construction
itself are thrown. -/
def mkBareissDecomposition? (A : Expr) : MetaM (Option BareissResult) := do
  let A ← instantiateMVars A
  let some (m, n, R, entries) ← matchMatrixLit? A
    | trace[Tactic.evalRank] "not a closed matrix literal{indentExpr A}"
      return none
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let .some _ ← trySynthInstanceQ q(CommRing $α)
    | trace[Tactic.evalRank] "expected the element type to be a commutative ring{indentExpr A}"
      return none
  let .some _ ← trySynthInstanceQ q(IsDomain $α)
    | trace[Tactic.evalRank] "expected the element type to be a domain{indentExpr A}"
      return none
  return some (← mkBareissDecomposition A m n α entries)

end Mathlib.Tactic.Echelon
