/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter6.Conservativity

/-!
# Chapter 6 strong surjectivity consequences

This file contains the object-level consequences of the strong-surjectivity package.

Book guide, paraphrasing the May 2026 draft:

- A strongly surjective functor has a section on cores. The definition itself is in
  `Chapter6/Definitions.lean`.
- Remark 6.3.2 extracts a chosen preimage object and a comparison to the target object. These are
  `stronglySurjectivePreimage` and `stronglySurjectiveBeta`.

Both declarations are admitted internal definitions and should be projections or short derivations
from `StronglySurjective`.
-/

@[expose] public section

namespace SCT

/- Objectwise consequences of Definition 6.3.1 are admitted temporarily while kept out of the model
interface. -/
internal_defs where
  /-- Chosen preimage object for strong surjectivity.
  Book target: Remark 6.3.2, derived from Definition 6.3.1.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def stronglySurjectivePreimage (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) (y : Obj D) : Obj C := sorry
  /-- Comparison from the chosen preimage to the target object; Remark 6.3.2.
  Book target: Remark 6.3.2, derived from Definition 6.3.1.
  Status: temporary sorry-admitted structural theorem package; not a model field. -/
  def stronglySurjectiveBeta (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) (y : Obj D) :
    NatIso terminalCat D
      (compFunctor terminalCat C D (stronglySurjectivePreimage C D F surj y) F) y :=
    sorry

end SCT
