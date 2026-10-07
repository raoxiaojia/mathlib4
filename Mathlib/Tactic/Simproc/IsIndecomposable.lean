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

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-! ### Directed graphs on `Fin n`, with sets of vertices as the set bits of a natural number -/

/-- The vertices reached from the set bits of `src` by following the edges `es` in order, an edge
counting only when it leaves a vertex already reached and is an edge of `adj`. -/
def reached {n : ℕ} (adj : Fin n → Fin n → Bool) (src : ℕ) (es : List (Fin n × Fin n)) : ℕ :=
  es.foldl (init := src) fun seen (p, c) ↦
    bif seen.testBit p && adj p c then seen ||| 1 <<< (c : ℕ) else seen

theorem reflTransGen_of_testBit_reached {n : ℕ} {adj : Fin n → Fin n → Bool} {a : Fin n}
    {src : ℕ} {es : List (Fin n × Fin n)}
    (hsrc : ∀ v : Fin n, src.testBit v → ReflTransGen (adj · ·) a v) {v : Fin n}
    (hv : (reached adj src es).testBit v) : ReflTransGen (adj · ·) a v := by
  induction es generalizing src with
  | nil => exact hsrc v hv
  | cons e es ih => exact ih (fun w hw ↦ by grind [Fin.ext_iff]) hv

/-- Whether no edge leaves the set of rows given by the set bits of `s`. -/
def isClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

/-- The adjacency with an edge from `i` to `j` when bit `i * n + j` of `bits` is set. -/
def packedAdj (n bits : ℕ) (i j : Fin n) : Bool :=
  bits.testBit (i * n + j)

/-- Whether no edge of the nonzero pattern `bits` of an `n × n` matrix, with entry `(i, j)` at bit
`i * n + j`, leaves the set of rows given by the set bits of `s`. Each row of `bits` is read at
once. -/
def isClosedPacked (n bits s : ℕ) : Bool :=
  (List.range n).all fun i ↦
    let row := bits >>> (i * n) &&& (2 ^ n - 1)
    !s.testBit i || (row &&& s) == row

theorem isClosed_of_isClosedPacked {n bits s : ℕ} (h : isClosedPacked n bits s = true) :
    isClosed (packedAdj n bits) s = true := by
  simp [isClosedPacked, Nat.eq_iff_testBit_eq] at h
  grind [isClosed, packedAdj]

/-! ### Certificates for the nonzero pattern of a matrix -/

variable {R : Type*} [Zero R] [DecidableEq R]

theorem isIndecomposable_of_reached {n : ℕ}
    {M : Matrix (Fin n) (Fin n) R} {adj : Fin n → Fin n → Bool}
    (hadj : ∀ i j, adj i j = decide (M i j ≠ 0)) {a : Fin n} {fwd bwd : List (Fin n × Fin n)}
    (hf : reached adj (1 <<< (a : ℕ)) fwd = 2 ^ n - 1)
    (hb : reached (fun i j ↦ adj j i) (1 <<< (a : ℕ)) bwd = 2 ^ n - 1) :
    M.IsIndecomposable := by
  have key {adj : Fin n → Fin n → Bool} {es : List (Fin n × Fin n)}
      (h : reached adj (1 <<< (a : ℕ)) es = 2 ^ n - 1) (v : Fin n) :
      ReflTransGen (adj · ·) a v :=
    reflTransGen_of_testBit_reached (src := 1 <<< (a : ℕ)) (es := es) (by grind) (by simp [h])
  refine (isIndecomposable_iff_reflTransGen M).2 fun i j ↦ ?_
  have hi := key hb i
  have hj := key hf j
  simp only [hadj, decide_eq_true_eq] at hi hj
  exact hi.swap.trans hj

theorem blockTriangular_of_isClosed {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {adj : Fin n → Fin n → Bool} (hadj : ∀ i j, adj i j = decide (M i j ≠ 0)) {s : ℕ}
    (h : isClosed adj s = true) :
    M.BlockTriangular (s.testBit ·) := by
  grind [isClosed, BlockTriangular, Bool.lt_iff]

/-- The nonzero entries of `l`, as the set bits of a natural number. -/
def listMask (l : List R) : ℕ :=
  match l with
  | [] => 0
  | a :: l => (if a = 0 then 0 else 1) ||| listMask l <<< 1

theorem testBit_listMask (l : List R) (j : ℕ) :
    (listMask l).testBit j = decide (l.getD j 0 ≠ 0) := by
  induction l generalizing j with
  | nil => simp [listMask]
  | cons a l ih =>
    cases j <;> by_cases a = 0 <;> simp_all [listMask, Nat.testBit_one_eq_true_iff_self_eq_zero]

/-- The nonzero entries of the `n × n` matrix with rows `rows`, as the set bits of a natural number
with entry `(i, j)` at bit `i * n + j`. -/
def packRows (n : ℕ) (rows : List (List R)) : ℕ :=
  match rows with
  | [] => 0
  | row :: rows => (listMask row &&& (2 ^ n - 1)) ||| packRows n rows <<< n

theorem testBit_packRows {n : ℕ} (rows : List (List R)) (i : ℕ) {j : ℕ} (hj : j < n) :
    (packRows n rows).testBit (i * n + j) = decide ((rows.getD i []).getD j 0 ≠ 0) := by
  induction rows generalizing i with
  | nil => simp [packRows]
  | cons row rows ih =>
    cases i <;> simp [packRows, testBit_listMask, hj, Nat.add_mul, Nat.add_right_comm _ n, ih]

theorem packedAdj_eq_of_packRows_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {rows : List (List R)} {bits : ℕ} (hM : M = ofLists n n rows) (hbits : packRows n rows = bits)
    (i j : Fin n) : packedAdj n bits i j = decide (M i j ≠ 0) := by
  rw [packedAdj, ← hbits, testBit_packRows rows i j.2, hM, ofLists_apply, ofList_apply]

theorem decide_ne_zero_eq_of_eq_of {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {f : Fin n → Fin n → R} (hM : M = of f) (i j : Fin n) :
    decide (f i j ≠ 0) = decide (M i j ≠ 0) := by
  rw [hM, of_apply]

end Mathlib.Tactic.Matrix.IsIndecomposable

end

public meta section

open Lean Meta Qq Matrix

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-- Breadth-first search from `root` along `adj`, returning the tree edges in discovery order and
the reached vertices. -/
def breadthFirstSearch (n : Nat) (adj : Nat → Nat → Bool) (root : Nat) :
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

/-- The outcome of searching a directed graph from and to vertex `0`. -/
inductive StrongConnectivity where
  /-- The graph is strongly connected, with the search trees `fwd` from `0` and `bwd` to `0`. -/
  | connected (fwd bwd : Array (Nat × Nat))
  /-- The graph is not strongly connected. No edge leaves the nonempty proper set of vertices
  `s`. -/
  | disconnected (s : Array Bool)

/-- Search the directed graph with adjacency matrix `pattern` from and to vertex `0`. -/
def decideStronglyConnected (pattern : Array (Array Bool)) : StrongConnectivity :=
  let n := pattern.size
  let adj (p c : Nat) : Bool := (pattern[p]!)[c]!
  let (fwd, fwdSeen) := breadthFirstSearch n adj 0
  -- The vertices reached from `0` are closed under the edges.
  if fwdSeen.any (!·) then .disconnected fwdSeen else
  let (bwd, bwdSeen) := breadthFirstSearch n (fun p c ↦ adj c p) 0
  -- The vertices not reaching `0` are closed under the edges.
  if bwdSeen.any (!·) then .disconnected (bwdSeen.map (!·)) else
  .connected fwd bwd

/-- The nonzero entries of the matrix that `view` builds, row by row, evaluated by the kernel one
row at a time, or `none` when the kernel cannot decide which entries are zero. -/
def evalPattern? {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α)) {n : Nat}
    (view : MatrixView α q(Fin $n) q(Fin $n)) : MetaM (Option (Array (Array Bool))) := do
  let masks : Array Q(Nat) ← match view with
    | .literal _ _ _ _ _ A => pure <| A.rows.toArray.map fun row ↦ q(listMask $(mkListLitQ row))
    | .functional f => Array.ofFnM (n := n) fun i ↦ do
      let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
      return q(Nat.ofBits fun j ↦ decide ($f $iQ j ≠ 0))
  let env ← getEnv
  return masks.mapM fun mask ↦
    match Kernel.whnf env {} mask with
    | .ok (.lit (.natVal m)) => some (Array.ofFn (n := n) fun j ↦ m.testBit j)
    | _ => none

/-- The nonzero pattern `pattern` of a square matrix of size `n`, as the set bits of a natural
number with entry `(i, j)` at bit `i * n + j`. -/
def packPattern (n : Nat) (pattern : Array (Array Bool)) : Nat :=
  pattern.foldr (fun row bits ↦ bits <<< n ||| Nat.ofBits (n := n) (row[·]!)) 0

/-- Prove `M.IsIndecomposable` from the search trees `fwd` from vertex `0` and `bwd` to it in the
nonzero pattern `pattern` of `M`. -/
def certifyIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    {n : Nat} {M : Q(Matrix (Fin $n) (Fin $n) $α)} (view : MatrixView α q(Fin $n) q(Fin $n))
    (pf : Q($M = $(view.toMatrix))) (pattern : Array (Array Bool)) (fwd bwd : Array (Nat × Nat)) :
    MetaM Q(($M).IsIndecomposable) := do
  let ⟨adj, hadj⟩ : (adj : Q(Fin $n → Fin $n → Bool)) × Q(∀ i j, $adj i j = decide ($M i j ≠ 0)) ←
    match view, pf with
    | .literal zα' _ _ _ _ A, pf => do
      -- `parse` stores the instance it is given and reads the dimensions of `A` off the type
      -- `Fin n` of `M`.
      have : $zα' =Q $zα := ⟨⟩
      have pf : Q($M = ofLists $n $n $(A.lit)) := pf
      let bitsQ : Q(Nat) := mkNatLitQ (packPattern n pattern)
      let hbits ← mkDecideProofQ q(packRows $n $(A.lit) = $bitsQ)
      let adj : Q(Fin $n → Fin $n → Bool) := q(packedAdj $n $bitsQ)
      pure ⟨adj, q(packedAdj_eq_of_packRows_eq $pf $hbits)⟩
    | .functional f, pf =>
      let adj : Q(Fin $n → Fin $n → Bool) := q(fun i j ↦ decide ($f i j ≠ 0))
      pure ⟨adj, q(decide_ne_zero_eq_of_eq_of $pf)⟩
  let root : Q(Fin $n) ← mkNumeral q(Fin $n) 0
  let fwdQ ← mkEdgeListLitQ n fwd
  let bwdQ ← mkEdgeListLitQ n bwd
  let hf ← mkDecideProofQ q(reached $adj (1 <<< ($root : Nat)) $fwdQ = 2 ^ $n - 1)
  let hb ← mkDecideProofQ q(reached (fun i j ↦ $adj j i) (1 <<< ($root : Nat)) $bwdQ = 2 ^ $n - 1)
  return q(isIndecomposable_of_reached $hadj $hf $hb)

/-- Prove `¬M.IsIndecomposable` from a nonempty proper set `s` of vertices of the nonzero pattern
`pattern` of `M` that no edge leaves. -/
def certifyNotIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (dα : Q(DecidableEq $α)) {n : Nat} {M : Q(Matrix (Fin $n) (Fin $n) $α)}
    (view : MatrixView α q(Fin $n) q(Fin $n)) (pf : Q($M = $(view.toMatrix)))
    (pattern : Array (Array Bool)) (s : Array Bool) : MetaM Q(¬($M).IsIndecomposable) := do
  let (some i, some j) := (s.findIdx? id, s.findIdx? (!·))
    | throwError "reduceIsIndecomposable: the set {s} is empty or full"
  let maskQ : Q(Nat) := mkNatLitQ (Nat.ofBits (n := n) (s[·]!))
  let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
  let jQ : Q(Fin $n) ← mkNumeral q(Fin $n) j
  let hij ← mkDecideProofQ q(Nat.testBit $maskQ $iQ ≠ Nat.testBit $maskQ $jQ)
  match view, pf with
  | .literal zα' _ _ _ _ A, pf =>
    -- `parse` stores the instance it is given and reads the dimensions of `A` off the type
    -- `Fin n` of `M`.
    have : $zα' =Q $zα := ⟨⟩
    have pf : Q($M = ofLists $n $n $(A.lit)) := pf
    let bitsQ : Q(Nat) := mkNatLitQ (packPattern n pattern)
    let hbits ← mkDecideProofQ q(packRows $n $(A.lit) = $bitsQ)
    let hc ← mkDecideProofQ q(isClosedPacked $n $bitsQ $maskQ = true)
    return q((blockTriangular_of_isClosed (packedAdj_eq_of_packRows_eq $pf $hbits)
      (isClosed_of_isClosedPacked $hc)).not_isIndecomposable $hij)
  | .functional f, pf =>
    let hc ← mkDecideProofQ q(isClosed (fun i j ↦ decide ($f i j ≠ 0)) $maskQ = true)
    return q((blockTriangular_of_isClosed (decide_ne_zero_eq_of_eq_of $pf) $hc).not_isIndecomposable
      $hij)

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
  let ⟨view, hM⟩ ← MatrixView.parse zα M
  let some pattern ← evalPattern? zα dα view | return .continue
  match decideStronglyConnected pattern with
  | .connected fwd bwd =>
    let pf ← certifyIsIndecomposable zα dα view hM pattern fwd bwd
    return .done { expr := q(True), proof? := q(eq_true $pf) }
  | .disconnected s =>
    let pf ← certifyNotIsIndecomposable zα dα view hM pattern s
    return .done { expr := q(False), proof? := q(eq_false $pf) }

end Mathlib.Tactic.Matrix.IsIndecomposable

open Mathlib.Tactic.Matrix.IsIndecomposable

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix `M` indexed
by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
