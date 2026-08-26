/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
public import Mathlib.Tactic.Echelon.Rat

/-!
# Certificate construction for the Bareiss decomposition

The certificate constructors for the `Echelon.Decomposition` of a matrix literal.
`mkCertificate` builds the certificate from decomposition data, with the certificate
conditions proven by kernel-checked `decide`. `mkCastCertificate` builds the certificate of a
matrix without kernel-decidable equality from the rational values of its entries: the
certificate is built over the value carrier (`ℤ` or `ℚ`) and transported along the cast
ring homomorphism (`Decomposition.map`); the only obligation at the element type is the
entrywise cast equation, closed by `norm_num`.

## Main definitions

- `mkCertificate`: build the certificate from the decomposition data.
- `mkCastCertificate`: build the certificate over the value carrier and transport it.
- `certifyDecomposition`: prove the certificate conditions by kernel-checked `decide`.
- `mkCastEq`: prove the entrywise cast equation between a literal and a mapped literal.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Build the numeral of `i` in `Fin $n`. -/
def mkFinNumeral (n : ℕ) (i : ℕ) : MetaM Q(Fin $n) :=
  mkNumeral q(Fin $n) i

/-- Build the pivot literal `![↑c₀, …, ⊤, …] : Fin m → WithTop (Fin n)`, sending the
first rows to their pivot columns and the remaining rows to `⊤`. -/
def mkPivotLit (m n : Nat) (pivots : Array Nat) : MetaM Q(Fin $m → WithTop (Fin $n)) := do
  let entries : Array Q(WithTop (Fin $n)) ← Array.ofFnM (n := m) fun i => do
    if hi : i < pivots.size then
      return q(WithTop.some $(← mkFinNumeral n pivots[i]))
    else
      return q(⊤ : WithTop (Fin $n))
  return PiFin.mkLiteralQ (α := q(WithTop (Fin $n))) (n := m) fun i => entries[i]!

/-- Build the permutation `σ = swap a₀ b₀ * swap a₁ b₁ * ⋯` from the recorded swaps. -/
def mkPerm (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(Equiv.Perm (Fin $m)) := do
  let mut acc : Q(Equiv.Perm (Fin $m)) := q(Equiv.refl (Fin $m))
  for (a, b) in swaps do
    acc := q((Equiv.swap $(← mkFinNumeral m a) $(← mkFinNumeral m b)).trans $acc)
  return acc

/-- Prove the certificate condition `c` by a kernel-checked `decide`, with `name` naming
the condition in errors. -/
def certifyCondition (name : String) (c : Q(Prop)) : MetaM Q($c) := do
  let d ← mkDecide c
  let .ok r := Kernel.whnf (← getEnv) (← getLCtx) d
    | throwError "cannot verify the rank certificate: {name} does not reduce in the kernel"
  unless r.isConstOf ``Bool.true do
    throwError "cannot verify the rank certificate: {name} failed"
  mkDecideProofQ c

/-- Prove the three certificate conditions of the decomposition `(L, σ, pivot)` of `A`
with echelon form `U` by kernel-checked `decide`. -/
def certifyDecomposition {u : Level} {m n : ℕ} {α : Q(Type u)} (cr : Q(CommRing $α))
    (L : Q(Matrix (Fin $m) (Fin $m) $α)) (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (σ : Q(Equiv.Perm (Fin $m))) (pivot : Q(Fin $m → WithTop (Fin $n)))
    (U : Q(Matrix (Fin $m) (Fin $n) $α)) :
    MetaM (Q(($L * ($A).submatrix $σ id).IsPivotedBy $pivot) ×
      Q(($L).IsLowerTriangular) × Q(∀ i, ($L).diag i ≠ 0)) := do
  -- the product identity and the echelon-form conditions are certified separately, on
  -- the echelon form `U` computed by the elimination, so that the matrix mult check can
  -- be replaced by its own means
  let pfEq ← certifyCondition "the product identity"
    -- TODO: switch to a more efficient matrix mult check once implemented
    q($L * ($A).submatrix $σ id = $U)
  let pfU ← certifyCondition "the echelon-pivot condition" q(($U).IsPivotedBy $pivot)
  let pf₁ : Q(($L * ($A).submatrix $σ id).IsPivotedBy $pivot) :=
    q(Eq.mpr (congrArg (Matrix.IsPivotedBy · $pivot) $pfEq) $pfU)
  let pf₂ ← certifyCondition "lower triangularity of the transform"
    q(($L).IsLowerTriangular)
  let pf₃ ← certifyCondition "the nonzero diagonal of the transform"
    q(∀ i, ($L).diag i ≠ 0)
  return (pf₁, pf₂, pf₃)

/-- Prove the cast equation `A = B`: `Matrix.ext` with the entrywise cast equations
closed by `norm_num`. -/
def mkCastEq {u : Level} {m n : ℕ} {α : Q(Type u)}
    (A B : Q(Matrix (Fin $m) (Fin $n) $α)) : MetaM Expr := do
  let entryEqs : Q(Prop) := q(∀ i j, $A i j = ($B) i j)
  -- a fixed simp set suffices: binder expansion, matrix-literal entry access, and the
  -- cast-homomorphism unfolding; norm_num closes the entrywise cast equations
  let thms ← [``Fin.forall_fin_succ, ``IsEmpty.forall_iff, ``Matrix.cons_val_zero,
    ``Matrix.cons_val_succ, ``Matrix.of_apply, ``Matrix.map_apply,
    ``Int.coe_castRingHom, ``Rat.coe_castHom, ``true_and].foldlM (·.addConst ·)
    ({} : SimpTheorems)
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let some pf ← (← Meta.NormNum.deriveSimp ctx true entryEqs).ofTrue
    | throwError "cannot verify the entry cast equations{indentExpr entryEqs}"
  mkAppM ``Matrix.ext #[pf]

/-- Build the `Echelon.Decomposition` certificate of `A` from the decomposition data,
with the certificate conditions proven by kernel-checked `decide`
(`certifyDecomposition`). -/
def mkCertificate {u : Level} {m n : ℕ} {α : Q(Type u)} (cr : Q(CommRing $α))
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (d : BareissData Expr) :
    MetaM Q(Echelon.Decomposition $A) := do
  have L : Q(Matrix (Fin $m) (Fin $m) $α) :=
    Matrix.mkLiteralQ (α := α) (m := m) (n := m) (.of fun i j => (d.L[i]!)[j]!)
  let σ ← mkPerm m d.swaps
  let pivot ← mkPivotLit m n d.pivot
  have U : Q(Matrix (Fin $m) (Fin $n) $α) :=
    Matrix.mkLiteralQ (α := α) (m := m) (n := n) (.of fun i j => (d.U[i]!)[j]!)
  let (pf₁, pf₂, pf₃) ← certifyDecomposition cr L A σ pivot U
  return q(⟨$L, $σ, $pivot, $pf₁, $pf₂, $pf₃⟩)

/-- Build the certificate of `A` from a certificate over the value carrier `β`
(`mkCertificate`), transported along the cast ring homomorphism `hom`
(`Decomposition.map` and `Decomposition.congr`); the only obligation at the element type
is the entrywise cast equation (`mkCastEq`). `mkEntry` builds the numeral of an entry
value in `β`; `values` are the values of the input and `d` the decomposition data over
the integer values. Returns the certificate together with the decomposition data over
`β`. -/
def mkCastCertificate {u : Level} {m n : ℕ} {α : Q(Type u)} {β : Q(Type)} (cr : Q(CommRing $α))
    (cβ : Q(CommRing $β)) (homE hinjE : Expr) (mkEntry : Rat → MetaM Expr)
    (A : Q(Matrix (Fin $m) (Fin $n) $α)) (values : Array (Array Rat))
    (d : BareissData Int) : MetaM (Q(Echelon.Decomposition $A) × BareissData Expr) := do
  -- `homE` cannot be a typed `Q($β →+* $α)` parameter: the caller's hom (`Rat.castHom`)
  -- carries `DivisionRing`-path instances in its type, which the signature's
  -- `CommRing`-path spelling does not match at reducible transparency
  have hom : Q($β →+* $α) := homE
  have hinj : Q(Function.Injective ⇑$hom) := hinjE
  let aLits ← values.mapM (·.mapM mkEntry)
  let d' : BareissData Expr ← d.mapM (mkIntNumeral β)
  have A' : Q(Matrix (Fin $m) (Fin $n) $β) :=
    Matrix.mkLiteralQ (α := β) (m := m) (n := n) (.of fun i j => (aLits[i]!)[j]!)
  let cert ← mkCertificate cβ A' d'
  have hA : Q($A = ($A').map $hom) := ← mkCastEq A q(($A').map $hom)
  return (q((($cert).map $hom $hinj).congr ($hA).symm), d')

end Mathlib.Tactic.Echelon
