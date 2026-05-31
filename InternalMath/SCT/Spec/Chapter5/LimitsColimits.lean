/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter5.Fibrations

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
  syntax_sort LimitCone (J : SCat) (C : SCat) (D : Diagram J C) : Type u
  /-- Colimit-cocone witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ColimitCocone (J : SCat) (C : SCat) (D : Diagram J C) : Type u
  /-- `C` admits limits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort HasLimitsOfShape (J : SCat) (C : SCat) : Type u
  /-- `C` admits colimits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort HasColimitsOfShape (J : SCat) (C : SCat) : Type u
  /-- Right adjoint limit functor to constant diagrams.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque limitFunctor (J : SCat) (C : SCat) (h : HasLimitsOfShape J C) :
    Functor (funCat J C) C
  /-- Left adjoint colimit functor to constant diagrams.
  Book context:Chapter 5 of the SCT book. -/
  lf_opaque colimitFunctor (J : SCat) (C : SCat) (h : HasColimitsOfShape J C) :
    Functor (funCat J C) C

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
