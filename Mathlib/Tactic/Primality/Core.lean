/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)

/-!
# Primality certificates

The result type shared by the certificate families, and the proof by `norm_num` that they use for
small numbers.

TODO: add variants of Pocklington certificates, with the minimal theory they need.
-/

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 18

/-- The proof of primality of a number, or the numbers whose primality blocked it. -/
abbrev PrimalityResult := Except (Array Nat) Q(Nat.Primes)

/-- Proves `p` prime by `norm_num`'s trial division. -/
def proveByNormNum (p : Nat) : MetaM PrimalityResult := do
  have pQ : Q(Nat) := mkRawNatLit p
  let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $pQ) | return .error #[p]
  return .ok q(⟨$pQ, $pf⟩)

end Mathlib.Tactic.Primality
