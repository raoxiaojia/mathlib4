/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Batteries.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Matrix.OfLists
public import Mathlib.Tactic.Matrix.View

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
by evaluation.

The nonzero pattern is computed by the kernel too, so it agrees with the equality the certificates
are checked against.

A `!![…]` literal is packed into one natural number, with entry `(i, j)` at bit `i * n + j`, and
both certificates are checked against that number, since reading the literal by position costs the
kernel a walk per entry. Any other matrix is read entry by entry, at the entries a certificate
names.

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
    {M : Matrix (Fin n) (Fin n) R} {adj : Fin n → Fin n → Bool}
    (hadj : ∀ i j, adj i j = decide (M i j ≠ 0)) {a : Fin n} {fwd bwd : List (Fin n × Fin n)}
    (hf : reachesAll adj (1 <<< (a : ℕ)) fwd = true)
    (hb : reachesAll (fun i j ↦ adj j i) (1 <<< (a : ℕ)) bwd = true) :
    M.IsIndecomposable := by
  have hseen {adj : Fin n → Fin n → Bool} (v : Fin n) (hv : (1 <<< (a : ℕ)).testBit v) :
      ReflTransGen (adj · ·) a v := by
    grind
  refine (isIndecomposable_iff_reflTransGen M).2 fun i j ↦ ?_
  have hi := reflTransGen_of_reachesAll hb hseen i
  have hj := reflTransGen_of_reachesAll hf hseen j
  simp only [hadj, decide_eq_true_eq] at hi hj
  exact (reflTransGen_swap.1 hi).trans hj

/-- Whether no edge leaves the set of rows given by the set bits of `s`. -/
def isClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

theorem blockTriangular_of_isClosed {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} {adj : Fin n → Fin n → Bool}
    (hadj : ∀ i j, adj i j = decide (M i j ≠ 0)) {s : ℕ} (h : isClosed adj s = true) :
    M.BlockTriangular (s.testBit ·) := by
  grind [isClosed, BlockTriangular, Bool.lt_iff]

/-- The nonzero entries of `l`, as the set bits of a natural number. -/
def listMask [Zero R] [DecidableEq R] (l : List R) : ℕ :=
  match l with
  | [] => 0
  | a :: l => (if a = 0 then 0 else 1) ||| listMask l <<< 1

theorem testBit_listMask [Zero R] [DecidableEq R] (l : List R) (j : ℕ) :
    (listMask l).testBit j = decide (l.getD j 0 ≠ 0) := by
  induction l generalizing j with
  | nil => simp [listMask]
  | cons a l ih =>
    cases j <;> by_cases a = 0 <;> simp_all [listMask, Nat.testBit_one_eq_true_iff_self_eq_zero]

/-- The nonzero entries of the `n × n` matrix with rows `rows`, as the set bits of a natural number
with entry `(i, j)` at bit `i * n + j`. -/
def packRows [Zero R] [DecidableEq R] (n : ℕ) (rows : List (List R)) : ℕ :=
  match rows with
  | [] => 0
  | row :: rows => (listMask row &&& (2 ^ n - 1)) ||| packRows n rows <<< n

theorem testBit_packRows [Zero R] [DecidableEq R] {n : ℕ} (rows : List (List R)) (i : ℕ)
    {j : ℕ} (hj : j < n) :
    (packRows n rows).testBit (i * n + j) = decide ((rows.getD i []).getD j 0 ≠ 0) := by
  induction rows generalizing i with
  | nil => simp [packRows]
  | cons row rows ih =>
    cases i with
    | zero => simp [packRows, Nat.testBit_shiftLeft, testBit_listMask, hj]
    | succ i =>
      have h := ih i
      have hle : n ≤ (i + 1) * n + j := by nlinarith
      simp only [packRows, Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
        Nat.testBit_shiftLeft, List.getD_cons_succ]
      have : (i + 1) * n + j - n = i * n + j := by rw [Nat.succ_mul]; lia
      simp [this, h, hle]

theorem testBit_eq_of_packRows_eq {n : ℕ} [Zero R] [DecidableEq R]
    {M : Matrix (Fin n) (Fin n) R} {rows : List (List R)} {P : ℕ} (hM : M = ofLists n n rows)
    (hP : packRows n rows = P) (i j : Fin n) : P.testBit (i * n + j) = decide (M i j ≠ 0) := by
  subst hM hP
  simp [testBit_packRows rows i j.2, ofLists_apply, ofList_apply]

/-- Whether no edge of the nonzero pattern `P` of an `n × n` matrix, with entry `(i, j)` at bit
`i * n + j`, leaves the set of rows given by the set bits of `s`. Each row of `P` is read at
once. -/
def isClosedPacked (n P s : ℕ) : Bool :=
  (List.range n).all fun i ↦
    let row := P >>> (i * n) &&& (2 ^ n - 1)
    !s.testBit i || (row &&& s) == row

theorem isClosed_of_isClosedPacked {n P s : ℕ} (h : isClosedPacked n P s = true) :
    isClosed (fun i j : Fin n ↦ P.testBit (i * n + j)) s = true := by
  simp only [isClosedPacked, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  simp only [isClosed, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true']
  intro i
  refine (h i i.2).imp id fun hi j ↦ ?_
  have := congrArg (Nat.testBit · j) hi
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, j.2] at this
  grind

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

/-- The nonzero pattern of a square matrix `M` of size `n`, with the adjacency the kernel checks
certificates against. -/
structure NonzeroPattern {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    (n : Nat) (M : Q(Matrix (Fin $n) (Fin $n) $α)) where
  /-- The nonzero entries of `M`, as the set bits of a natural number with entry `(i, j)` at bit
  `i * n + j`. -/
  bits : Nat
  /-- The adjacency the certificates are stated with. -/
  adj : Q(Fin $n → Fin $n → Bool)
  /-- The proof that `adj` is the nonzero pattern of `M`. -/
  proof : Q(∀ i j, $adj i j = decide ($M i j ≠ 0))
  /-- Prove that no edge of `adj` leaves the set given by the set bits of `s`. -/
  certifyIsClosed (s : Q(Nat)) : MetaM Q(isClosed $adj $s = true)

/-- The nonzero pattern of `M`, evaluated by the kernel, or `none` when the kernel cannot decide
which entries are zero. A literal is packed by `packRows` and any other matrix is read entry by
entry. -/
def mkPattern? {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α)) (n : Nat)
    {M : Q(Matrix (Fin $n) (Fin $n) $α)} (view : MatrixView zα n n M) :
    MetaM (Option (NonzeroPattern zα dα n M)) := do
  let env ← getEnv
  match view with
  | .literal l pf =>
    let .ok (.lit (.natVal bits)) := Kernel.whnf env {} q(packRows $n $(l.lit)) | return none
    let P : Q(Nat) := mkNatLitQ bits
    let hP ← mkDecideProofQ q(packRows $n $(l.lit) = $P)
    let adj : Q(Fin $n → Fin $n → Bool) := q(fun i j ↦ Nat.testBit $P ((i : Nat) * $n + (j : Nat)))
    return some {
      bits, adj
      proof := q(testBit_eq_of_packRows_eq $pf $hP)
      certifyIsClosed s := do
        let hc ← mkDecideProofQ q(isClosedPacked $n $P $s = true)
        return q(isClosed_of_isClosedPacked $hc) }
  | .functional =>
    let mut bits := 0
    for i in 0...n do
      let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
      let .ok (.lit (.natVal row)) := Kernel.whnf env {} q(Nat.ofBits fun j ↦ decide ($M $iQ j ≠ 0))
        | return none
      bits := bits ||| row <<< (i * n)
    let adj : Q(Fin $n → Fin $n → Bool) := q(fun i j ↦ decide ($M i j ≠ 0))
    return some {
      bits, adj
      proof := q(fun _ _ ↦ rfl)
      certifyIsClosed s := mkDecideProofQ q(isClosed $adj $s = true) }

/-- Prove `¬M.IsIndecomposable` from the set `s` of rows whose entries outside `s` vanish, with
`i` in `s` and `j` outside it. -/
def certifyNotIsIndecomposable {u : Level} {α : Q(Type u)} {zα : Q(Zero $α)}
    {dα : Q(DecidableEq $α)} {n : Nat} {M : Q(Matrix (Fin $n) (Fin $n) $α)}
    (pat : NonzeroPattern zα dα n M) (s : Array Bool) (i j : Nat) :
    MetaM Q(¬($M).IsIndecomposable) := do
  let maskQ : Q(Nat) := mkNatLitQ (Nat.ofBits (n := n) (s[·]!))
  let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
  let jQ : Q(Fin $n) ← mkNumeral q(Fin $n) j
  let hij ← mkDecideProofQ q(Nat.testBit $maskQ $iQ ≠ Nat.testBit $maskQ $jQ)
  let hc ← pat.certifyIsClosed maskQ
  return q((blockTriangular_of_isClosed $(pat.proof) $hc).not_isIndecomposable $hij)

/-- Rewrite `M.IsIndecomposable` to `True` or `False` from the nonzero pattern `pat` of `M`. -/
def proveIsIndecomposable {u : Level} {α : Q(Type u)} {zα : Q(Zero $α)}
    {dα : Q(DecidableEq $α)} {n : Nat} {M : Q(Matrix (Fin $n) (Fin $n) $α)}
    (pat : NonzeroPattern zα dα n M) : MetaM Simp.Result := do
  let adj (p c : Nat) : Bool := pat.bits.testBit (p * n + c)
  let (fwd, fwdSeen) := spanningTree n adj 0
  -- The vertices reached from `0` are closed under the edges.
  if let some j := fwdSeen.findIdx? (!·) then
    let pf ← certifyNotIsIndecomposable pat fwdSeen 0 j
    return { expr := q(False), proof? := q(eq_false $pf) }
  let (bwd, bwdSeen) := spanningTree n (fun p c ↦ adj c p) 0
  -- The vertices not reaching `0` are closed under the edges.
  if let some i := bwdSeen.findIdx? (!·) then
    let pf ← certifyNotIsIndecomposable pat (bwdSeen.map (!·)) i 0
    return { expr := q(False), proof? := q(eq_false $pf) }
  let root : Q(Fin $n) ← mkNumeral q(Fin $n) 0
  let fwdQ ← mkEdgeListLitQ n fwd
  let bwdQ ← mkEdgeListLitQ n bwd
  let hf ← mkDecideProofQ q(reachesAll $(pat.adj) (1 <<< ($root : Nat)) $fwdQ = true)
  let hb ← mkDecideProofQ
    q(reachesAll (fun i j ↦ $(pat.adj) j i) (1 <<< ($root : Nat)) $bwdQ = true)
  let pf : Q(($M).IsIndecomposable) := q(isIndecomposable_of_reachesAll $(pat.proof) $hf $hb)
  return { expr := q(True), proof? := q(eq_true $pf) }

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
  let dα : Q(DecidableEq $α) ← match ← trySynthInstanceQ q(DecidableEq $α) with
    | .some dα => pure dα
    | _ => return .continue
  let view ← MatrixView.parse zα n n M
  let some pat ← mkPattern? zα dα n view
    | trace[Tactic.reduceIsIndecomposable]
        "the kernel cannot decide which entries are zero{indentExpr M}"
      return .continue
  return .done (← proveIsIndecomposable pat)

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix `M` indexed
by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
