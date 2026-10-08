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

The question is essentially to determine whether the graph corresponding to `M` is strongly
connected. The Boolean adjacency matrix of `M` has entry `(i, j)` true when `M i j ≠ 0`,
currently evaluated by the kernel; for the functional representation this is the bottleneck,
and future optimisation is possible by considering compiled evaluation of the function.

There is an existing implementation of Tarjan's algorithm at `Order.Graph.Tarjan`, but it doesn't
return a witness for the strongly connected components, and the algorithm is also an overkill.
This simproc instead simply runs two bfs on the graph from vertex `0` forwards and backwards.
If all vertices are reached in both passes, then the indecomposability is certified by the two
search trees. Otherwise, `M` is decomposable, witnessed by a set of rows whose entries outside
the set evaluate to 0.

The Boolean adjacency matrix of a `!![…]` literal is packed into one natural number, with entry
`(i, j)` at bit `i * n + j`, and both certificates are checked against that number, since reading
the literal by position costs the kernel a walk per entry.
-/

@[expose] public section

open Matrix Relation

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-! ### Directed graphs on `Fin n`, with sets of vertices as the set bits of a natural number -/

/-- The vertices reached from the set bits of `src` by following the edges `es` in order, an edge
counting only when it leaves a vertex already reached and is an edge of `adj`. -/
def reached {n : ℕ} (adj : Fin n → Fin n → Bool) (src : ℕ) (es : List (Fin n × Fin n)) : ℕ :=
  es.foldl (init := src) fun visited (p, c) ↦
    bif visited.testBit p && adj p c then visited ||| 1 <<< (c : ℕ) else visited

theorem reflTransGen_of_testBit_reached {n : ℕ} {adj : Fin n → Fin n → Bool} {a : Fin n}
    {src : ℕ} {es : List (Fin n × Fin n)}
    (hsrc : ∀ v : Fin n, src.testBit v → ReflTransGen (fun i j ↦ adj i j) a v) {v : Fin n}
    (hv : (reached adj src es).testBit v) : ReflTransGen (fun i j ↦ adj i j) a v := by
  induction es generalizing src with
  | nil => exact hsrc v hv
  | cons e es ih => exact ih (fun w hw ↦ by grind [Fin.ext_iff]) hv

/-- Whether no edge leaves the set of vertices given by the set bits of `s`. -/
def isClosed {n : ℕ} (adj : Fin n → Fin n → Bool) (s : ℕ) : Bool :=
  (List.finRange n).all fun i ↦ !s.testBit i ||
    (List.finRange n).all fun j ↦ s.testBit j || !adj i j

/-- The `n × n` Boolean adjacency matrix packed into `bits`, with entry `(i, j)` at bit
`i * n + j`. -/
def packedAdj (n bits : ℕ) (i j : Fin n) : Bool :=
  bits.testBit (i * n + j)

/-- Whether no edge of the `n × n` Boolean adjacency matrix packed into `bits`, with entry `(i, j)`
at bit `i * n + j`, leaves the set of vertices given by the set bits of `s`. Each row of `bits` is
read at once. -/
def isClosedPacked (n bits s : ℕ) : Bool :=
  (List.range n).all fun i ↦
    let row := bits >>> (i * n) &&& (2 ^ n - 1)
    !s.testBit i || (row &&& s) == row

theorem isClosed_of_isClosedPacked {n bits s : ℕ} (h : isClosedPacked n bits s = true) :
    isClosed (packedAdj n bits) s = true := by
  simp [isClosedPacked, Nat.eq_iff_testBit_eq] at h
  grind [isClosed, packedAdj]

/-! ### Certificates for a matrix from its Boolean adjacency matrix -/

variable {R : Type*} [Zero R]

theorem isIndecomposable_of_reached {n : ℕ}
    {M : Matrix (Fin n) (Fin n) R} {adj : Fin n → Fin n → Bool}
    (hadj : ∀ i j, adj i j ↔ M i j ≠ 0) {a : Fin n} {fwd bwd : List (Fin n × Fin n)}
    (hf : reached adj (1 <<< (a : ℕ)) fwd = 2 ^ n - 1)
    (hb : reached (fun i j ↦ adj j i) (1 <<< (a : ℕ)) bwd = 2 ^ n - 1) :
    M.IsIndecomposable := by
  have key {adj : Fin n → Fin n → Bool} {es : List (Fin n × Fin n)}
      (h : reached adj (1 <<< (a : ℕ)) es = 2 ^ n - 1) (v : Fin n) :
      ReflTransGen (fun i j ↦ adj i j) a v :=
    reflTransGen_of_testBit_reached (src := 1 <<< (a : ℕ)) (es := es) (by grind) (by simp [h])
  refine (isIndecomposable_iff_reflTransGen M).2 fun i j ↦ ?_
  have hi := key hb i
  have hj := key hf j
  simp only [hadj] at hi hj
  exact hi.swap.trans hj

theorem not_isIndecomposable_of_isClosed {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {adj : Fin n → Fin n → Bool} (hadj : ∀ i j, adj i j ↔ M i j ≠ 0) {s : ℕ}
    (h : isClosed adj s = true) {i j : Fin n} (hij : s.testBit i ≠ s.testBit j) :
    ¬M.IsIndecomposable := by
  intro hM
  obtain ⟨a, ha⟩ := (isIndecomposable_iff_blockTriangular_const M).1 hM (s.testBit ·)
    (by grind [isClosed, BlockTriangular, Bool.lt_iff])
  simp_all [funext_iff]

variable [DecidableEq R]

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

/-- The Boolean adjacency matrix of the `n × n` matrix with rows `rows`, as the set bits of a
natural number with entry `(i, j)` at bit `i * n + j`. -/
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

theorem packedAdj_iff_of_packRows_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    {rows : List (List R)} {bits : ℕ} (hM : M = ofLists n n rows) (hbits : packRows n rows = bits)
    (i j : Fin n) : packedAdj n bits i j ↔ M i j ≠ 0 := by
  rw [packedAdj, ← hbits, testBit_packRows rows i j.2, hM, ofLists_apply, ofList_apply,
    decide_eq_true_iff]

/-- The Boolean adjacency matrix of the function `f`, with an edge from `i` to `j` when
`f i j ≠ 0`. -/
def adjOf {n : ℕ} (f : Fin n → Fin n → R) (i j : Fin n) : Bool :=
  decide (f i j ≠ 0)

theorem adjOf_iff_of_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {f : Fin n → Fin n → R}
    (hM : M = of f) (i j : Fin n) : adjOf f i j ↔ M i j ≠ 0 := by
  rw [adjOf, hM, of_apply, decide_eq_true_iff]

end Mathlib.Tactic.Matrix.IsIndecomposable

end

public meta section

open Lean Meta Qq Matrix

namespace Mathlib.Tactic.Matrix.IsIndecomposable

/-- Breadth-first search from `root` along `adj`, returning the tree edges in discovery order and
the reached vertices. -/
def bfs (n : Nat) (adj : Nat → Nat → Bool) (root : Nat) :
    Array (Nat × Nat) × Array Bool := Id.run do
  let mut visited := (Array.replicate n false).set! root true
  let mut tree := #[]
  let mut current := #[root]
  while !current.isEmpty do
    let mut next := #[]
    for p in current do
      for c in 0...n do
        if adj p c && !visited[c]! then
          visited := visited.set! c true
          tree := tree.push (p, c)
          next := next.push c
    current := next
  return (tree, visited)

/-- The list literal of the edges `edges`. -/
def mkEdgeListLitQ (n : Nat) (edges : Array (Nat × Nat)) : MetaM Q(List (Fin $n × Fin $n)) := do
  let es ← edges.toList.mapM fun (p, c) ↦ do
    let pQ : Q(Fin $n) ← mkNumeral q(Fin $n) p
    let cQ : Q(Fin $n) ← mkNumeral q(Fin $n) c
    return q(($pQ, $cQ))
  return mkListLitQ (α := q(Fin $n × Fin $n)) es

/-- The outcome of searching a directed graph from and to vertex `0`. -/
inductive StrongConnectivity where
  /-- The graph is strongly connected, with the spanning out-tree `outTree` from `0` and in-tree
  `inTree` to `0`. -/
  | connected (outTree inTree : Array (Nat × Nat))
  /-- The graph is not strongly connected. No edge leaves the nonempty proper set of vertices
  `closedSet`. -/
  | disconnected (closedSet : Array Bool)

/-- Search the directed graph with Boolean adjacency matrix `adjMatrix` from and to vertex `0`. -/
def decideStronglyConnected (adjMatrix : Array (Array Bool)) : StrongConnectivity :=
  let n := adjMatrix.size
  let adj (p c : Nat) : Bool := (adjMatrix[p]!)[c]!
  let (outTree, fromRoot) := bfs n adj 0
  -- The vertices reached from `0` are closed under the edges.
  if !fromRoot.all id then .disconnected fromRoot else
  let (inTree, toRoot) := bfs n (fun p c ↦ adj c p) 0
  -- The vertices not reaching `0` are closed under the edges.
  if !toRoot.all id then .disconnected (toRoot.map not) else
  .connected outTree inTree

/-- The Boolean adjacency matrix of the matrix that `view` builds, evaluated by the kernel, or
`none` when the kernel cannot decide which entries are zero. A literal is evaluated in one call to
`packRows`, the number its certificates are checked against, and a function one row at a time.
Compiled evaluation with `evalExpr` is faster on matrices given by functions, but in a `module`
file the compiled code may only call definitions available at compile time, a set that depends on
the importing file's whole import graph. -/
def evalAdjMatrix? {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α)) {n : Nat}
    (view : MatrixView α q(Fin $n) q(Fin $n)) : MetaM (Option (Array (Array Bool))) := do
  let env ← getEnv
  let eval (e : Q(Nat)) : Option Nat :=
    match Kernel.whnf env {} e with
    | .ok (.lit (.natVal m)) => some m
    | _ => none
  match view with
  | .literal _ _ _ _ _ A =>
    let some bits := eval q(packRows $n $(A.lit)) | return none
    return some <| Array.ofFn (n := n) fun i ↦ Array.ofFn (n := n) fun j ↦ bits.testBit (i * n + j)
  | .functional f =>
    OptionT.run <| Array.ofFnM (n := n) fun i ↦ do
      let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
      let some row := eval q(Nat.ofBits (adjOf $f $iQ)) | failure
      return Array.ofFn (n := n) (row.testBit ·)

/-- The Boolean adjacency matrix `adjMatrix` of `M`, as a numeral with entry `(i, j)` at bit
`i * n + j`, with the proof that it is that of `M`. -/
def provePackedAdj {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    (n : Nat) {M : Q(Matrix (Fin $n) (Fin $n) $α)} (lit : Q(List (List $α)))
    (pf : Q($M = ofLists $n $n $lit)) (adjMatrix : Array (Array Bool)) :
    (bits : Q(Nat)) × Q(∀ i j, packedAdj $n $bits i j ↔ $M i j ≠ 0) :=
  let bits : Q(Nat) := mkNatLitQ <|
    adjMatrix.foldr (fun row acc ↦ acc <<< n ||| Nat.ofBits (n := n) (row[·]!)) 0
  have : $bits =Q packRows $n $lit := ⟨⟩
  ⟨bits, q(packedAdj_iff_of_packRows_eq $pf rfl)⟩

/-- Prove `A.matrix.IsIndecomposable` from the spanning out-tree `outTree` from vertex `0` and
in-tree `inTree` to it in the graph of the Boolean adjacency matrix `adjMatrix` of `A.matrix`. -/
def certifyIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (dα : Q(DecidableEq $α))
    {n : Nat} (A : MatrixWithView α q(Fin $n) q(Fin $n)) (adjMatrix : Array (Array Bool))
    (outTree inTree : Array (Nat × Nat)) : MetaM Q(($(A.matrix)).IsIndecomposable) := do
  let root : Q(Fin $n) ← mkNumeral q(Fin $n) 0
  let outTreeQ ← mkEdgeListLitQ n outTree
  let inTreeQ ← mkEdgeListLitQ n inTree
  match (dependent := true) A with
  | ⟨M, view, pf⟩ =>
    let ⟨adj, hadj⟩ :
        (adj : Q(Fin $n → Fin $n → Bool)) × Q(∀ i j, $adj i j ↔ $M i j ≠ 0) :=
      match view with
      | .literal _ _ _ _ _ L =>
        -- `parse` reads the dimensions of `L` off the type `Fin n` of `M`.
        let ⟨bits, hadj⟩ := provePackedAdj zα dα n (M := M) L.lit pf adjMatrix
        ⟨q(packedAdj $n $bits), hadj⟩
      | .functional f => ⟨q(adjOf $f), q(adjOf_iff_of_eq $pf)⟩
    let hout ← mkDecideProofQ q(reached $adj (1 <<< ($root : Nat)) $outTreeQ = 2 ^ $n - 1)
    let hin ← mkDecideProofQ
      q(reached (fun i j ↦ $adj j i) (1 <<< ($root : Nat)) $inTreeQ = 2 ^ $n - 1)
    return q(isIndecomposable_of_reached $hadj $hout $hin)

/-- Prove `¬A.matrix.IsIndecomposable` from a nonempty proper set `closedSet` of vertices that no
edge of the Boolean adjacency matrix `adjMatrix` of `A.matrix` leaves. -/
def certifyNotIsIndecomposable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α))
    (dα : Q(DecidableEq $α)) {n : Nat} (A : MatrixWithView α q(Fin $n) q(Fin $n))
    (adjMatrix : Array (Array Bool)) (closedSet : Array Bool) :
    MetaM Q(¬($(A.matrix)).IsIndecomposable) := do
  let (some i, some j) := (closedSet.findIdx? id, closedSet.findIdx? not)
    | throwError "reduceIsIndecomposable: the closed set {closedSet} is empty or full"
  let closedSetQ : Q(Nat) := mkNatLitQ (Nat.ofBits (n := n) (closedSet[·]!))
  let iQ : Q(Fin $n) ← mkNumeral q(Fin $n) i
  let jQ : Q(Fin $n) ← mkNumeral q(Fin $n) j
  let hij ← mkDecideProofQ q(Nat.testBit $closedSetQ $iQ ≠ Nat.testBit $closedSetQ $jQ)
  match (dependent := true) A with
  | ⟨M, .literal zα' _ _ _ _ L, pf⟩ =>
    -- `parse` stores the instance it is given and reads the dimensions of `L` off the type
    -- `Fin n` of `M`.
    have : $zα' =Q $zα := ⟨⟩
    let ⟨bits, hadj⟩ := provePackedAdj zα dα n (M := M) L.lit pf adjMatrix
    let hc ← mkDecideProofQ q(isClosedPacked $n $bits $closedSetQ = true)
    return q(not_isIndecomposable_of_isClosed $hadj (isClosed_of_isClosedPacked $hc) $hij)
  | ⟨_, .functional f, pf⟩ =>
    let hc ← mkDecideProofQ q(isClosed (adjOf $f) $closedSetQ = true)
    return q(not_isIndecomposable_of_isClosed (adjOf_iff_of_eq $pf) $hc $hij)

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
  let A ← MatrixWithView.parse zα M
  let some adjMatrix ← evalAdjMatrix? zα dα A.view | return .continue
  match decideStronglyConnected adjMatrix with
  | .connected outTree inTree =>
    let pf ← certifyIsIndecomposable zα dα A adjMatrix outTree inTree
    return .done { expr := q(True), proof? := q(eq_true $pf) }
  | .disconnected closedSet =>
    let pf ← certifyNotIsIndecomposable zα dα A adjMatrix closedSet
    return .done { expr := q(False), proof? := q(eq_false $pf) }

end Mathlib.Tactic.Matrix.IsIndecomposable

open Mathlib.Tactic.Matrix.IsIndecomposable

/-- `Matrix.reduceIsIndecomposable` decides `M.IsIndecomposable` for a closed matrix `M` indexed
by `Fin n` with `n` a numeral, whose entries have an equality the kernel can decide. -/
simproc_decl Matrix.reduceIsIndecomposable (Matrix.IsIndecomposable _) :=
  reduceIsIndecomposableCore
