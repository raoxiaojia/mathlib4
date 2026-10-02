/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Batteries.Data.Nat.Basic
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
def reachesAll {n : ℕ} (adj : Fin n → Fin n → Bool) (seen : ℕ) (es : List (Fin n × Fin n)) : Bool :=
  match es with
  | [] => seen == 2 ^ n - 1
  | (p, c) :: es => seen.testBit p && adj p c && reachesAll adj (seen ||| 1 <<< (c : ℕ)) es

theorem reflTransGen_of_reachesAll {n : ℕ} {adj : Fin n → Fin n → Bool} {a : Fin n} {seen : ℕ}
    {es : List (Fin n × Fin n)} (h : reachesAll adj seen es = true)
    (hseen : ∀ v : Fin n, seen.testBit v → ReflTransGen (adj · ·) a v) (v : Fin n) :
    ReflTransGen (adj · ·) a v := by
  induction es generalizing seen with grind [reachesAll, Fin.ext_iff]

theorem isIndecomposable_of_reachesAll {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} {a : Fin n} {fwd bwd : List (Fin n × Fin n)}
    (hf : reachesAll (fun i j ↦ decide (M i j ≠ 0)) (1 <<< (a : ℕ)) fwd = true)
    (hb : reachesAll (fun i j ↦ decide (M j i ≠ 0)) (1 <<< (a : ℕ)) bwd = true) :
    M.IsIndecomposable := by
  have hseen {adj : Fin n → Fin n → Bool} (v : Fin n) (hv : (1 <<< (a : ℕ)).testBit v) :
      ReflTransGen (adj · ·) a v := by
    grind
  refine (isIndecomposable_iff_reflTransGen M).2 fun i j ↦ ?_
  have hi := reflTransGen_of_reachesAll hb hseen i
  have hj := reflTransGen_of_reachesAll hf hseen j
  simp only [decide_eq_true_eq] at hi hj
  exact (reflTransGen_swap.1 hi).trans hj

/-- Whether no edge leaves the set of rows given by the set bits of `s`. -/
def rowsClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

theorem blockTriangular_of_rowsClosed {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} {s : ℕ}
    (h : rowsClosed (fun i j ↦ decide (M i j ≠ 0)) s = true) :
    M.BlockTriangular (s.testBit ·) := by
  grind [rowsClosed, BlockTriangular, Bool.lt_iff]

/-- The nonzero entries of `l`, as the set bits of a natural number. -/
def listMask [Zero R] [DecidableEq R] (l : List R) : ℕ :=
  match l with
  | [] => 0
  | a :: l => (if a = 0 then 0 else 1) ||| listMask l <<< 1

end Mathlib.Tactic.Matrix

end

public meta section

open Lean Meta Qq Matrix

initialize registerTraceClass `Tactic.reduceIsIndecomposable

namespace Mathlib.Tactic.Matrix

/-- Breadth-first search from `root` along `adj`, returning the tree edges in discovery order and
the reached vertices. -/
def spanningTree (n : Nat) (adj : Nat → Nat → Bool) (root : Nat) :
    Array (Nat × Nat) × Array Bool := Id.run do
  let mut seen := (Array.replicate n false).set! root true
  let mut edges := #[]
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for p in frontier do
      for c in 0...n do
        if adj p c && !seen[c]! then
          seen := seen.set! c true
          edges := edges.push (p, c)
          next := next.push c
    frontier := next
  return (edges, seen)

/-- The list literal of the edges `edges`. -/
def mkEdgeListLitQ (n : Nat) (edges : Array (Nat × Nat)) : MetaM Q(List (Fin $n × Fin $n)) := do
  let es ← edges.toList.mapM fun (p, c) ↦ do
    let pQ : Q(Fin $n) ← mkNumeral q(Fin $n) p
    let cQ : Q(Fin $n) ← mkNumeral q(Fin $n) c
    return q(($pQ, $cQ))
  return mkListLitQ (α := q(Fin $n × Fin $n)) es

/-- The nonzero pattern from the row masks `masks`, each evaluated by the kernel, or `none` when a
mask does not reduce to a literal. -/
def evalPattern? (masks : Array Q(Nat)) : MetaM (Option (Array Nat)) := do
  let env ← getEnv
  return masks.mapM fun mask ↦
    match Kernel.whnf env {} mask with
    | .ok (.lit (.natVal m)) => some m
    | _ => none

/-- The row masks of `M`, by `listMask` on each row of a literal and by `Nat.ofBits` otherwise. -/
def mkRowMasks {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α)) (n : Nat)
    (M : Q(Matrix (Fin $n) (Fin $n) $α)) : MetaM (Array Q(Nat)) := do
  match ← matchMatrixLit? M with
  | some (_, _, _, entries) =>
    return entries.map fun row ↦
      let rowQ : List Q($α) := row.toList
      q(listMask $(mkListLitQ rowQ))
  | none =>
    Array.ofFnM (n := n) fun i ↦ do
      let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
      return q(Nat.ofBits fun j ↦ decide ($M $iQ j ≠ 0))

/-- Prove `¬M.IsIndecomposable` from the set `s` of rows whose entries outside `s` vanish, with
`i` in `s` and `j` outside it. -/
def certifyNotIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (dα : Q(DecidableEq $α)) (n : Nat) (M : Q(Matrix (Fin $n) (Fin $n) $α)) (s : Array Bool)
    (i j : Nat) : MetaM Q(¬($M).IsIndecomposable) := do
  let maskQ : Q(Nat) := mkNatLitQ (Nat.ofBits (n := n) (s[·]!))
  let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
  let jQ : Q(Fin $n) ← mkNumeral q(Fin $n) j
  let hc ← mkDecideProofQ q(rowsClosed (fun i j ↦ decide ($M i j ≠ 0)) $maskQ = true)
  let hij ← mkDecideProofQ q(Nat.testBit $maskQ $iQ ≠ Nat.testBit $maskQ $jQ)
  return q((blockTriangular_of_rowsClosed $hc).not_isIndecomposable $hij)

/-- Rewrite `M.IsIndecomposable` to `True` or `False` from the nonzero pattern `adj` of `M`. -/
def proveIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    (n : Nat) (M : Q(Matrix (Fin $n) (Fin $n) $α)) (adj : Array Nat) : MetaM Simp.Result := do
  let (fwd, fwdSeen) := spanningTree n (fun p c ↦ adj[p]!.testBit c) 0
  -- The vertices reached from `0` are closed under the edges.
  if let some j := fwdSeen.findIdx? (!·) then
    let pf ← certifyNotIsIndecomposable zα dα n M fwdSeen 0 j
    return { expr := q(False), proof? := q(eq_false $pf) }
  let (bwd, bwdSeen) := spanningTree n (fun p c ↦ adj[c]!.testBit p) 0
  -- The vertices not reaching `0` are closed under the edges.
  if let some i := bwdSeen.findIdx? (!·) then
    let pf ← certifyNotIsIndecomposable zα dα n M (bwdSeen.map (!·)) i 0
    return { expr := q(False), proof? := q(eq_false $pf) }
  let root : Q(Fin $n) ← mkNumeral q(Fin $n) 0
  let fwdQ ← mkEdgeListLitQ n fwd
  let bwdQ ← mkEdgeListLitQ n bwd
  let hf ← mkDecideProofQ
    q(reachesAll (fun i j ↦ decide ($M i j ≠ 0)) (1 <<< ($root : Nat)) $fwdQ = true)
  let hb ← mkDecideProofQ
    q(reachesAll (fun i j ↦ decide ($M j i ≠ 0)) (1 <<< ($root : Nat)) $bwdQ = true)
  return { expr := q(True), proof? := q(eq_true (isIndecomposable_of_reachesAll $hf $hb)) }

/-- Core of the `Matrix.reduceIsIndecomposable` simproc. -/
def reduceIsIndecomposableCore : Simp.Simproc := fun e ↦ do
  let e ← instantiateMVars e
  let_expr Matrix.IsIndecomposable finN R zR M := e | return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let_expr Fin nE := finN | return .continue
  let some n ← getNatValue? nE | return .continue
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have zα : Q(Zero $α) := zR
  if n == 0 then
    have M : Q(Matrix (Fin 0) (Fin 0) $α) := M
    let pf : Q(($M).IsIndecomposable) := q((isIndecomposable_iff_reflTransGen $M).2 (·.elim0))
    return .done { expr := q(True), proof? := q(eq_true $pf) }
  have M : Q(Matrix (Fin $n) (Fin $n) $α) := M
  let .some dα ← trySynthInstanceQ q(DecidableEq $α) | return .continue
  let some adj ← evalPattern? (← mkRowMasks zα dα n M)
    | trace[Tactic.reduceIsIndecomposable]
        "the kernel cannot decide which entries are zero{indentExpr M}"
      return .continue
  return .done (← proveIsIndecomposable zα dα n M adj)

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix `M` indexed
by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
