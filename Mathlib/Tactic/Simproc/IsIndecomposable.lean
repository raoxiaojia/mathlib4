/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Matrix.Parsing
import Mathlib.Util.Qq

/-!
# Simproc deciding `Matrix.IsIndecomposable`

`Matrix.reduceIsIndecomposable` rewrites `M.IsIndecomposable` to `True` or `False` for a closed
square matrix `M` indexed by `Fin n`, whose entries have an equality the kernel can decide.

## Implementation notes

The simproc searches the nonzero pattern of `M` from vertex `0`, forwards and backwards. An
indecomposable matrix is certified by the two search trees, which show that every vertex is
reached from `0` and reaches `0`. A decomposable matrix is certified by a set of rows whose entries
outside the set vanish, a block-triangular colouring of `M`. The kernel checks either certificate
by evaluation and reads only the entries it names.

The nonzero pattern is computed by the kernel too, one bitmask per row, so it agrees with the
equality the certificates are checked against. The rows of a `!![…]` literal are passed as lists
and read in one pass, since reading the literal by position costs the kernel a walk per entry.

Reached vertices are tracked as the set bits of a natural number, whose bit operations the kernel
evaluates on literals.
-/

@[expose] public section

open Matrix Relation

namespace Mathlib.Tactic.Matrix

variable {R : Type*}

/-- Whether the edges `es`, taken in order, each leave a vertex already reached, the reached
vertices being the set bits of `seen`, and reach every vertex. -/
def reachesAll {n : ℕ} (adj : Fin n → Fin n → Bool) (seen : ℕ) : List (Fin n × Fin n) → Bool
  | [] => seen == 2 ^ n - 1
  | (p, c) :: es => seen.testBit p && adj p c && reachesAll adj (seen ||| 1 <<< (c : ℕ)) es

theorem reflTransGen_of_reachesAll {n : ℕ} {adj : Fin n → Fin n → Bool} {a : Fin n} {seen : ℕ}
    {es : List (Fin n × Fin n)} (h : reachesAll adj seen es = true)
    (hseen : ∀ v : Fin n, seen.testBit v → ReflTransGen (adj · ·) a v) (v : Fin n) :
    ReflTransGen (adj · ·) a v := by
  induction es generalizing seen with
  | nil => simp_all [reachesAll]
  | cons e es ih =>
    obtain ⟨p, c⟩ := e
    simp only [reachesAll, Bool.and_eq_true] at h
    refine ih h.2 fun w hw ↦ ?_
    grind [Fin.ext_iff]

theorem isIndecomposable_of_reachesAll {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} (a : Fin n) (fwd bwd : List (Fin n × Fin n))
    (hf : reachesAll (fun i j ↦ decide (M i j ≠ 0)) (1 <<< (a : ℕ)) fwd = true)
    (hb : reachesAll (fun i j ↦ decide (M j i ≠ 0)) (1 <<< (a : ℕ)) bwd = true) :
    M.IsIndecomposable := by
  have hseen {adj : Fin n → Fin n → Bool} (v : Fin n) (hv : (1 <<< (a : ℕ)).testBit v) :
      ReflTransGen (adj · ·) a v := by
    grind
  rw [isIndecomposable_iff_reflTransGen]
  intro i j
  have hi := reflTransGen_of_reachesAll hb hseen i
  have hj := reflTransGen_of_reachesAll hf hseen j
  simp only [decide_eq_true_eq] at hi hj
  exact (reflTransGen_swap.1 hi).trans hj

/-- Whether no edge leaves the set of rows given by the set bits of `s`. -/
def rowsClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

theorem blockTriangular_of_rowsClosed {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} {s : ℕ} (h : rowsClosed (fun i j ↦ decide (M i j ≠ 0)) s) :
    M.BlockTriangular fun k ↦ s.testBit k := by
  intro i j hij
  rw [Bool.lt_iff] at hij
  simp only [rowsClosed, List.all_eq_true, List.mem_finRange, forall_const] at h
  grind

/-- The nonzero entries of row `i` of `M`, as the set bits of a natural number. -/
def rowMask {n : ℕ} [Zero R] [DecidableEq R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) : ℕ :=
  (List.finRange n).foldr (init := 0) fun j acc ↦ if M i j = 0 then acc else acc ||| 1 <<< (j : ℕ)

/-- The nonzero entries of `l`, as the set bits of a natural number. -/
def listMask [Zero R] [DecidableEq R] : List R → ℕ
  | [] => 0
  | a :: l => (if a = 0 then 0 else 1) ||| listMask l <<< 1

end Mathlib.Tactic.Matrix

end

public meta section

open Lean Meta Qq Matrix

initialize registerTraceClass `Tactic.reduceIsIndecomposable

namespace Mathlib.Tactic.Matrix

/-- Breadth-first search from `r` along `adj`, returning the tree edges in discovery order and the
reached vertices. -/
def spanningTree (adj : Array (Array Bool)) (r : Nat) : Array (Nat × Nat) × Array Bool := Id.run do
  let mut seen := (Array.replicate adj.size false).set! r true
  let mut edges := #[]
  let mut frontier := #[r]
  while !frontier.isEmpty do
    let mut next := #[]
    for p in frontier do
      for c in 0...adj.size do
        if (adj[p]!)[c]! && !seen[c]! then
          seen := seen.set! c true
          edges := edges.push (p, c)
          next := next.push c
    frontier := next
  return (edges, seen)

/-- The list literal of the edges `edges`. -/
def mkEdgeList (n : Nat) (edges : Array (Nat × Nat)) : MetaM Q(List (Fin $n × Fin $n)) := do
  let es ← edges.toList.mapM fun (p, c) ↦ do
    let pQ : Q(Fin $n) ← mkNumeral q(Fin $n) p
    let cQ : Q(Fin $n) ← mkNumeral q(Fin $n) c
    return q(($pQ, $cQ))
  return mkListLitQ (α := q(Fin $n × Fin $n)) es

/-- The nonzero pattern from the row masks `masks`, each evaluated by the kernel, or `none` when a
mask does not reduce to a literal. -/
def evalPattern (n : Nat) (masks : Array Q(Nat)) : MetaM (Option (Array (Array Bool))) := do
  let env ← getEnv
  let lctx ← getLCtx
  return masks.mapM fun mask ↦
    match Kernel.whnf env lctx mask with
    | .ok (.lit (.natVal m)) => some (Array.ofFn (n := n) fun j ↦ m.testBit j)
    | _ => none

/-- The row masks of `M`, by `listMask` on each row of a literal and by `rowMask` otherwise. -/
def rowMasks {u : Level} {R : Q(Type u)} (zR : Q(Zero $R)) (dR : Q(DecidableEq $R)) (n : Nat)
    (M : Q(Matrix (Fin $n) (Fin $n) $R)) : MetaM (Array Q(Nat)) := do
  match ← matchMatrixLit? M with
  | some (_, _, _, entries) =>
    return entries.map fun row ↦
      have rowQ : List Q($R) := row.toList
      q(listMask $(mkListLitQ rowQ))
  | none =>
    Array.ofFnM (n := n) fun i ↦ do
      let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
      return q(rowMask $M $iQ)

/-- Prove `¬M.IsIndecomposable` from the set `s` of rows whose entries outside `s` vanish, with
`i` in `s` and `j` outside it. -/
def refuteIndecomposable {u : Level} {R : Q(Type u)} (zR : Q(Zero $R)) (dR : Q(DecidableEq $R))
    (n : Nat) (M : Q(Matrix (Fin $n) (Fin $n) $R)) (s : Array Bool) (i j : Nat) :
    MetaM Q(¬($M).IsIndecomposable) := do
  let mask := Id.run do
    let mut mask := 0
    for k in 0...n do
      if s[k]! then mask := mask ||| 1 <<< k
    return mask
  have maskQ : Q(Nat) := mkNatLitQ mask
  let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
  let jQ : Q(Fin $n) ← mkNumeral q(Fin $n) j
  let hc ← mkDecideProofQ q(rowsClosed (fun i j ↦ decide ($M i j ≠ 0)) $maskQ = true)
  let hij ← mkDecideProofQ q(Nat.testBit $maskQ $iQ ≠ Nat.testBit $maskQ $jQ)
  return q((blockTriangular_of_rowsClosed $hc).not_isIndecomposable $hij)

/-- Rewrite `M.IsIndecomposable` to `True` or `False` from the nonzero pattern `adj` of `M`. -/
def proveIndecomposable {u : Level} {R : Q(Type u)} (zR : Q(Zero $R)) (dR : Q(DecidableEq $R))
    (n : Nat) (M : Q(Matrix (Fin $n) (Fin $n) $R)) (adj : Array (Array Bool)) :
    MetaM Simp.Result := do
  let (fwd, fwdSeen) := spanningTree adj 0
  -- the vertices reached from `0` are closed under the edges
  if let some j := fwdSeen.findIdx? (!·) then
    return { expr := q(False),
             proof? := q(eq_false $(← refuteIndecomposable zR dR n M fwdSeen 0 j)) }
  let adjT := Array.ofFn (n := n) fun i ↦ Array.ofFn (n := n) fun j ↦ (adj[j]!)[i]!
  let (bwd, bwdSeen) := spanningTree adjT 0
  -- the vertices not reaching `0` are closed under the edges
  if let some i := bwdSeen.findIdx? (!·) then
    return { expr := q(False),
             proof? := q(eq_false $(← refuteIndecomposable zR dR n M (bwdSeen.map (!·)) i 0)) }
  let root : Q(Fin $n) ← mkNumeral q(Fin $n) 0
  let fwdQ ← mkEdgeList n fwd
  let bwdQ ← mkEdgeList n bwd
  let hf ← mkDecideProofQ
    q(reachesAll (fun i j ↦ decide ($M i j ≠ 0)) (1 <<< ($root : Nat)) $fwdQ = true)
  let hb ← mkDecideProofQ
    q(reachesAll (fun i j ↦ decide ($M j i ≠ 0)) (1 <<< ($root : Nat)) $bwdQ = true)
  return { expr := q(True),
           proof? := q(eq_true (isIndecomposable_of_reachesAll $root $fwdQ $bwdQ $hf $hb)) }

/-- Core of the `Matrix.reduceIsIndecomposable` simproc. -/
def reduceIsIndecomposableCore : Simp.Simproc := fun e ↦ do
  let_expr Matrix.IsIndecomposable ι R zR M := e | return .continue
  let_expr Fin nE := ι
    | trace[Tactic.reduceIsIndecomposable] "the index type is not `Fin n`{indentExpr ι}"
      return .continue
  let some n ← getNatValue? nE
    | trace[Tactic.reduceIsIndecomposable] "the dimension is not a numeral{indentExpr nE}"
      return .continue
  let M ← instantiateMVars M
  if M.hasFVar || M.hasMVar then
    trace[Tactic.reduceIsIndecomposable] "the matrix is not closed{indentExpr M}"
    return .continue
  let v ← getDecLevel R
  have R : Q(Type v) := R
  have zR : Q(Zero $R) := zR
  if n == 0 then
    have M : Q(Matrix (Fin 0) (Fin 0) $R) := M
    return .done { expr := q(True),
                   proof? := q(eq_true ((isIndecomposable_iff_reflTransGen $M).2 (·.elim0))) }
  have M : Q(Matrix (Fin $n) (Fin $n) $R) := M
  let .some dR ← trySynthInstanceQ q(DecidableEq $R)
    | trace[Tactic.reduceIsIndecomposable] "no `DecidableEq` instance for the entries{indentExpr R}"
      return .continue
  let some adj ← evalPattern n (← rowMasks zR dR n M)
    | trace[Tactic.reduceIsIndecomposable]
        "the kernel cannot decide which entries are zero{indentExpr M}"
      return .continue
  return .done (← proveIndecomposable zR dR n M adj)

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix `M` indexed
by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
