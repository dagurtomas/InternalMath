/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter6.Definitions

/-!
# Chapter 6 conservativity consequences

This file contains theorem statements about conservativity.

Book guide, paraphrasing the May 2026 draft:

- Fully faithful functors are conservative; this is `fullyFaithfulConservative`.
- Conservative functors reflect invertible morphisms; this is `conservativeReflectsIso`.

Both declarations are admitted internal definitions, not model fields. They should be proved from
the fully faithful and conservative criteria in `Chapter6/Definitions.lean`.
-/

@[expose] public section

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Fully faithful functors are conservative; Proposition 6.2.8.
  Book target: Proposition 6.2.8, fully faithful functors are conservative.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove using the arrow-map characterization and invertible morphisms.
  -/
  def fullyFaithfulConservative (C : SCat) (D : SCat) (F : Functor C D)
    (ff : FullyFaithful C D F) : Conservative C D F := sorry
  /-- Conservative functors reflect invertible morphisms.
  Book target: §6.2, conservative functors reflect invertible morphisms.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: unpack the conservative/core-pullback criterion. -/
  def conservativeReflectsIso (C : SCat) (D : SCat) (F : Functor C D)
    (cons : Conservative C D F) (f : Functor intervalCat C)
    (hf : InvertibleMorphism D (compFunctor f F)) : InvertibleMorphism C f := sorry

end SCT
