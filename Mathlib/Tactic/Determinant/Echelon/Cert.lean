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
public import Mathlib.Tactic.ReduceModChar
public meta import Mathlib.Tactic.Echelon.Bareiss
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Matrix.Parsing
public meta import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.ReduceModChar

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

/-- Prove the sign in the ring, `-(-(… 1))`, of a permutation of the shape `mkPerm` builds,
`(swap a b).trans (… (refl _))`, one lemma per swap. -/
partial def provePermSign {u : Level} {α : Q(Type u)} (_cr : Q(CommRing $α)) {m : ℕ}
    (σ : Q(Equiv.Perm (Fin $m))) :
    MetaM ((s : Q($α)) × Q(((Equiv.Perm.sign $σ : ℤ) : $α) = $s)) := do
  match_expr σ with
  | Equiv.refl _ =>
    -- `σ` is the matched term, so the lemmas are stated about it by an unchecked retyping
    let h : Expr := q(intCast_sign_refl (n := Fin $m) (α := $α))
    have h : Q(((Equiv.Perm.sign $σ : ℤ) : $α) = 1) := h
    return ⟨q(1), h⟩
  | Equiv.trans _ _ _ sw rest =>
    let_expr Equiv.swap _ _ a b := sw | throwError "expected a swap in{indentExpr σ}"
    have a : Q(Fin $m) := a
    have b : Q(Fin $m) := b
    have rest : Q(Equiv.Perm (Fin $m)) := rest
    let ⟨s, h⟩ ← provePermSign _cr rest
    let hab : Q($a ≠ $b) ← mkDecideProofQ q($a ≠ $b)
    let h' : Expr := q(intCast_sign_swap_trans $h $hab)
    have h' : Q(((Equiv.Perm.sign $σ : ℤ) : $α) = -$s) := h'
    return ⟨q(-$s), h'⟩
  | _ => throwError "expected a chain of swaps in{indentExpr σ}"

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
  let r ← mkBareissDecomposition _cr A entries
  -- the model is selected again for its entry certifier, which the result does not carry
  let certifier := (← modelFor α).entryCertifier?.getD mkDecideProofQ
  have c := r.cert
  have cert : Q(Echelon.Decomposition $A) := c.toDecomposition
  -- the diagonal products, left unevaluated: the certified identity evaluates them. The views
  -- rebuild the literals `c.L` and `c.U` of the certificate.
  have L := mkMatrixViews _cr m m r.data.L
  have U := mkMatrixViews _cr m m r.data.U
  have litL : Q(List (List $α)) := L.lit
  have litU : Q(List (List $α)) := U.lit
  let ⟨eL, hL⟩ := proveDiagProd _cr m litL L.entries
  let ⟨eU, hUdiag⟩ := proveDiagProd _cr m litU U.entries
  have hl : Q(∏ i, ofLists $m $m $litL i i = $eL) := q((prod_diag_ofLists $m $litL).trans $hL)
  have hu : Q(∏ i, ofLists $m $m $litU i i = $eU) :=
    q((prod_diag_ofLists $m $litU).trans $hUdiag)
  -- the sign of the certificate's permutation
  let ⟨s, hs⟩ ← provePermSign _cr c.σ
  -- the value, verified by the identity
  let candidates ← detCandidates _cr m r.data s eL eU
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
  -- the projections of `cert` reduce to the fields of `c`, and `c.L`, `c.U`, `c.σ` are the
  -- terms the views and `provePermSign` rebuilt, so the hypotheses transport by defeq
  have Um : Q(Matrix (Fin $m) (Fin $m) $α) := c.U
  have hU' : Q(($cert).L * ($A).submatrix ($cert).σ id = $Um) := c.mul_eq
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
    -- normalise the value where `norm_num` evaluates it, and reduce it modulo the
    -- characteristic where the ring is `ZMod n`
    let ctx ← readThe Simp.Context
    let r : Simp.Result := { expr := v, proof? := some pf }
    let r ← r.mkEqTrans (← try Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := false) (e := v)
      catch _ => pure { expr := v })
    let r ← r.mkEqTrans (← try Tactic.ReduceModChar.derive (e := r.expr)
      catch _ => pure { expr := r.expr })
    return some r
  catch ex =>
    trace[Tactic.evalDet] "{ex.toMessageData}"
    return none

end Mathlib.Tactic.Determinant
