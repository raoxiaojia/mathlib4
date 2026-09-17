/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Determinant.Echelon.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Bareiss
public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.Echelon.Bareiss
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Matrix.Parsing
public meta import Mathlib.Tactic.NormNum.Basic

/-!
# Determinants of matrix literals by echelon decomposition

`proveEchelonDet` evaluates the determinant of a square matrix literal with non-symbolic entries
through the certificate `Echelon.Decomposition A` of its Bareiss decomposition and
`Echelon.Decomposition.det_eq`: the determinant is read off the diagonals of the transform `L` and
the echelon form `U`, and the reading is certified by the identity `l * (s * v) = u` on the
diagonal products.

## Main definitions

- `proveEchelonDet`: produce the decomposition and elaborate a proof of `A.det = v`.
- `normDetEchelon?`: the `norm_det` branch for literals the echelon method handles.

## Implementation notes

The Bareiss elimination leaves the diagonal of `L` equal to the diagonal of `U` shifted by one
row, so the quotient of the diagonal products is the last pivot. The rational model rescales the
rows of its input and folds the scales into `L`, which breaks this shape; its ring then has a
division, and the quotient is evaluated by `norm_num` instead.
-/

public meta section

open Lean Meta Qq Mathlib.Tactic.Echelon Mathlib.Tactic.Matrix

initialize registerTraceClass `Tactic.evalDet

namespace Mathlib.Tactic.Determinant

/-- Rewrite `diagProd 0 m lit`, for `lit` the list literal of `rows`, to the product
`a₀ * (a₁ * (… * 1))` of the diagonal entries of the rows. -/
def proveDiagProd {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (m : ℕ)
    (lit : Q(List (List $α))) (rows : List (List Q($α))) :
    (e : Q($α)) × Q(diagProd 0 $m $lit = $e) :=
  let ⟨_, _, e, h⟩ := go _cr q(0) 0 rows
  ⟨e, mkExpectedPropHint h q(diagProd 0 $m $lit = $e)⟩
where
  /-- The chain of the equations from row `k` on; the row and count arguments are successor
  towers so that each step is one application of `diagProd_succ_cons`. The instance is passed
  again since a `where` function does not see the binders of its parent. -/
  go {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (kQ : Q(ℕ)) (k : ℕ) :
      List (List Q($α)) →
        (c : Q(ℕ)) × (rowsQ : Q(List (List $α))) × (e : Q($α)) × Q(diagProd $kQ $c $rowsQ = $e)
    | [] => ⟨q(0), q([]), q(1), q(diagProd_zero $kQ [])⟩
    | row :: rows =>
      let ⟨c, rowsQ, e, h⟩ := go _cr q($kQ + 1) (k + 1) rows
      have rowQ : Q(List $α) := mkListLitQ row
      have a : Q($α) := row.getD k q(0)
      have hd : Q(List.getD $rowQ $kQ 0 = $a) :=
        mkExpectedPropHint q(Eq.refl $a) q(List.getD $rowQ $kQ 0 = $a)
      ⟨q($c + 1), q($rowQ :: $rowsQ), q($a * $e), q(diagProd_succ_cons $hd $h)⟩

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` of the recorded swaps together with
its sign `s = ±1` in the ring. -/
def provePermSign {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (m : ℕ)
    (swaps : Array (Nat × Nat)) :
    MetaM ((σ : Q(Equiv.Perm (Fin $m))) × (s : Q($α)) ×
      Q(((Equiv.Perm.sign $σ : ℤ) : $α) = $s)) := do
  let mut σ : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  let mut positive := true
  let mut hσ : Expr := q(Equiv.Perm.sign_refl (α := Fin $m))
  for (a, b) in swaps do
    let ia ← mkFinNumeral m a
    let ib ← mkFinNumeral m b
    let hab : Q($ia ≠ $ib) ← mkDecideProofQ q($ia ≠ $ib)
    if positive then
      have h : Q(Equiv.Perm.sign $σ = 1) := hσ
      hσ := q(sign_swap_trans_of_sign_eq_one $h $hab)
    else
      have h : Q(Equiv.Perm.sign $σ = -1) := hσ
      hσ := q(sign_swap_trans_of_sign_eq_neg_one $h $hab)
    σ := q((Equiv.swap $ia $ib).trans $σ)
    positive := !positive
  if positive then
    have h : Q(Equiv.Perm.sign $σ = 1) := hσ
    return ⟨σ, q(1), q(intCast_sign_eq_one $h)⟩
  else
    have h : Q(Equiv.Perm.sign $σ = -1) := hσ
    return ⟨σ, q(-1), q(intCast_sign_eq_neg_one $h)⟩

/-- Candidate values of the determinant, read off the decomposition data: `0` on a pivot
shortfall; the last pivot with the sign of the swaps when the diagonal of `L` is the shifted
diagonal of `U`; and the quotient of the diagonal products `s * u / l` evaluated by `norm_num`
when the ring has a division. -/
def detCandidates {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (m : ℕ)
    (data : BareissData Expr) (s eL eU : Q($α)) : MetaM (List Q($α)) := do
  if m == 0 then return [q(1)]
  if data.pivot.size < m then return [q(0)]
  let mut candidates : Array Q($α) := #[]
  have zero : Q($α) := q(0)
  let diag (M : Array (Array Expr)) (k : ℕ) : Expr := (M.getD k #[]).getD k zero
  -- both diagonals are emitted by the model's one `mkEntry`, so equal values are equal terms
  if (List.range (m - 1)).all fun k => diag data.L (k + 1) == diag data.U k then
    have p : Q($α) := diag data.U (m - 1)
    let v : Q($α) := if data.swaps.size % 2 == 0 then p else q(-$p)
    candidates := candidates.push v
  if let .some dα ← trySynthInstanceQ q(Div $α) then
    have _dα : Q(Div $α) := dα
    try
      let r ← Mathlib.Meta.NormNum.derive q($s * $eU / $eL)
      have w : Q($α) := (← r.toSimpResult).expr
      candidates := candidates.push w
    catch _ => pure ()
  return candidates.toList

/-- Produce the Bareiss decomposition of the square matrix literal `A` with `entries`, its parsed
entries, and elaborate a proof of `A.det = v` for the value `v` read off the decomposition. -/
def proveEchelonDet {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) (_id : Q(IsDomain $α))
    (m : ℕ) (A : Q(Matrix (Fin $m) (Fin $m) $α)) (entries : Array (Array Expr)) :
    MetaM ((v : Q($α)) × Q(($A).det = $v)) := do
  let model ← modelFor α
  let data ← model.producer entries
  -- the decomposition certificate, as `certifyDecomposition` builds it, keeping the echelon form
  -- and the product equation
  have L := mkMatrixViews _cr m m data.L
  have U := mkMatrixViews _cr m m data.U
  have Aσ := mkMatrixViews _cr m m (data.rowOrder.map (entries[·]!))
  let ⟨σ, s, hs⟩ ← provePermSign _cr m data.swaps
  have cols : Q(List (Fin $m)) := ← mkPivotList m data.pivot
  have Lm := L.matrix
  have Aσm := Aσ.matrix
  have Um := U.matrix
  let hperm ← certifyPermEq A Aσm σ
  have hprod : Q($Lm * $Aσm = $Um) := ← certifyProductEq _cr L Aσ U model.entryCertifier?
  have hU : Q($Lm * ($A).submatrix $σ id = $Um) := q($hperm ▸ $hprod)
  let certifier := model.entryCertifier?.getD mkDecideProofQ
  have hpivot : Q(($Um).IsPivotedBy fun i : Fin $m ↦ pivotOfList $cols i) :=
    ← certifyPivotedBy _cr U cols data.pivot certifier
  let ⟨hlower, hdiag⟩ ← certifyLowerTriangularDiag _cr L certifier
  have hlower : Q(($Lm).IsLowerTriangular) := hlower
  have hdiag : Q(∀ i, ($Lm).diag i ≠ 0) := hdiag
  have cert : Q(Echelon.Decomposition $A) :=
    q(⟨$Lm, $σ, fun i : Fin $m ↦ pivotOfList $cols i, $hU ▸ $hpivot, $hlower, $hdiag⟩)
  -- the diagonal products, left unevaluated: the certified identity evaluates them
  have litL : Q(List (List $α)) := L.lit
  have litU : Q(List (List $α)) := U.lit
  let ⟨eL, hL⟩ := proveDiagProd _cr m litL L.entries
  let ⟨eU, hUdiag⟩ := proveDiagProd _cr m litU U.entries
  have hl : Q(∏ i, ofLists $m $m $litL i i = $eL) := q((prod_diag_ofLists $m $litL).trans $hL)
  have hu : Q(∏ i, ofLists $m $m $litU i i = $eU) :=
    q((prod_diag_ofLists $m $litU).trans $hUdiag)
  -- the value, verified by the identity
  let candidates ← detCandidates _cr m data s eL eU
  let mut result : Option ((v : Q($α)) × Q($eL * ($s * $v) = $eU)) := none
  for v in candidates do
    try
      let hv ← certifier q($eL * ($s * $v) = $eU)
      result := some ⟨v, hv⟩
      break
    catch ex =>
      trace[Tactic.evalDet] "the candidate value {v} is refuted: {ex.toMessageData}"
  let some ⟨v, hv⟩ := result
    | throwError "no candidate value of the determinant is certified"
  -- the projections of `cert` reduce to its fields, so the hypotheses transport by defeq
  have hU' : Q(($cert).L * ($A).submatrix ($cert).σ id = $Um) := hU
  have hl' : Q(∏ i, ($cert).L i i = $eL) := hl
  have hu' : Q(∏ i, $Um i i = $eU) := hu
  have hs' : Q(((Equiv.Perm.sign ($cert).σ : ℤ) : $α) = $s) := hs
  return ⟨v, q(Echelon.Decomposition.det_eq $cert $hU' $hl' $hu' $hs' $hv)⟩

/-- The `norm_det` branch for square matrix literals with non-symbolic entries over a domain the
echelon method handles: `none` where it does not apply or fails, leaving the term to the
fallback method. -/
def normDetEchelon? (e : Expr) : SimpM (Option Simp.Result) := do
  let_expr Matrix.det _ _ _ _ _ A := e | return none
  let A ← instantiateMVars A
  let some (m, n, R, entries) ← matchMatrixLit? A
    | trace[Tactic.evalDet] "not a closed matrix literal{indentExpr A}"
      return none
  unless m == n do return none
  match ← checkBareissApplicable R with
  | .error err =>
    trace[Tactic.evalDet] "{err}{indentExpr A}"
    return none
  | .ok _ => pure ()
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have _cr : Q(CommRing $α) := ← synthInstanceQ q(CommRing $α)
  have _id : Q(IsDomain $α) := ← synthInstanceQ q(IsDomain $α)
  have A : Q(Matrix (Fin $m) (Fin $m) $α) := A
  try
    let ⟨v, pf⟩ ← proveEchelonDet _cr _id m A entries
    -- normalise the value where `norm_num` evaluates it
    let ctx ← readThe Simp.Context
    let r : Simp.Result := { expr := v, proof? := some pf }
    let s ← try Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := false) (e := v)
      catch _ => pure { expr := v }
    return some (← r.mkEqTrans s)
  catch ex =>
    trace[Tactic.evalDet] "{ex.toMessageData}"
    return none

end Mathlib.Tactic.Determinant
