/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public meta import Mathlib.Tactic.Primality.Core

/-! # The `small` certificate method

Proves a small prime by `norm_num`'s trial division. Used as a base case in certificate ladders.
-/

open Lean Meta Elab Qq

namespace Mathlib.Tactic.Primality

/-- Syntax for the `small` method: just a numeric literal `n`, proved prime by trial division.

```lean
-- In a prime_cert% call:
prime_cert% [small {2; 3; 5; 7}, ...]
```
-/
public syntax small_spec := num

public meta def mkSmallProof : PrimeCertMethod ``small_spec := fun stx _ ↦ match stx with
  | `(small_spec| $n:num) => do
    have n := n.getNat
    return ⟨n, mkNatLit n, ← proveSmallPrime n⟩
  | _ => throwUnsupportedSyntax

@[prime_cert small] public meta def PrimeCertExt.small : PrimeCertExt where
  syntaxName := ``small_spec
  methodName := ``mkSmallProof

end Mathlib.Tactic.Primality
