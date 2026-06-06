/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter5.Fibrations

/-!
# Chapter 5 limits, colimits, and local fibration structure

This file adds a thin vocabulary layer for limits and colimits and connects absolute fibration
structure to its local version in context.

Book guide, paraphrasing the May 2026 draft:

- A diagram of shape `J` in `C` is a functor `J ⟶ C`; this is `Diagram`.
- `coneCat` and `coconeCat` are the cone and cocone categories over a diagram.
- `LimitCone`, `ColimitCocone`, `HasLimitsOfShape`, and `HasColimitsOfShape` are admitted
  `syntax_def` packages. They give names to the limit/colimit vocabulary while the universal
  property packages are still being designed.
- `limitFunctor` and `colimitFunctor` are admitted projections from the corresponding
  has-limits/has-colimits packages.
- `locallyCocartesianOfCocartesian` and `locallyCartesianOfCartesian` connect absolute fibration
  witnesses with the contextual fibration vocabulary of Chapter 4.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter5

  /-- Pushout-indexing shape `⌜ = * ★ {0,1}` for spans.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque pushoutShapeCat : SCat
  /-- A diagram of shape `J` in `C`.  Book context: Chapter 5 of the SCT book. -/
  syntax_abbrev Diagram (J : SCat) (C : SCat) := Functor J C
  /-- Cone category over a diagram.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque coneCat (J : SCat) (C : SCat) (D : Diagram J C) : SCat
  /-- Cocone category under a diagram.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque coconeCat (J : SCat) (C : SCat) (D : Diagram J C) : SCat
  /-- Limit-cone witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_def LimitCone (J : SCat) (C : SCat) (D : Diagram J C) : Type u := sorry
  /-- Colimit-cocone witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_def ColimitCocone (J : SCat) (C : SCat) (D : Diagram J C) : Type u := sorry
  /-- `C` admits limits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_def HasLimitsOfShape (J : SCat) (C : SCat) : Type u := sorry
  /-- `C` admits colimits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_def HasColimitsOfShape (J : SCat) (C : SCat) : Type u := sorry

namespace SCT

/- Projection API for the admitted limit and colimit packages. -/
internal_defs where
  /-- Right adjoint limit functor to constant diagrams.  Book context: Chapter 5 of the SCT book. -/
  def limitFunctor (J : SCat) (C : SCat) (h : HasLimitsOfShape J C) :
    Functor (funCat J C) C := sorry
  /-- Left adjoint colimit functor to constant diagrams.
  Book context:Chapter 5 of the SCT book. -/
  def colimitFunctor (J : SCat) (C : SCat) (h : HasColimitsOfShape J C) :
    Functor (funCat J C) C := sorry

end SCT


extend_type_theory SCT where

  model_section Chapter5

  /-- Absolute cocartesian fibrations are locally cocartesian in context; Chapter 5 structure data.
  -/
  lf_opaque locallyCocartesianOfCocartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    LocallyCocartesianFibrationWitness E B p fib
  /-- Absolute cartesian fibrations are locally cartesian in context; Chapter 5 structure data. -/
  lf_opaque locallyCartesianOfCartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib) :
    LocallyCartesianFibrationWitness E B p fib
