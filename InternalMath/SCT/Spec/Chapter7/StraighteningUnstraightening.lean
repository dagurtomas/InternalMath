/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.FiberwiseLocalization

@[expose] public section

extend_type_theory SCT where

  model_section Chapter7

  /-- The groupoid-universe classifier recovers the underlying anima-category; Section 7.6.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def animaClassifyingEquiv : (A : Anima) ⇒
      CatEquiv (animaCat A)
        (classifiedTotalCat groupoidUniverse groupoidUniverseWitness terminalCat
          (animaClassifyingMap A)) :=
    fun A => smallClassifyingEquiv groupoidUniverse groupoidUniverseWitness
      (animaCat A) (animaSmall A)

namespace SCT

internal_defs where
  /-- Category of small cocartesian fibrations over a base.
  Book target: Theorem 7.7.8.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def cocartesianFibrationsOverCat (U : SCat) (u : UniverseWitness U) (B : SCat) :
    SCat := sorry

  /-- Straightening/unstraightening equivalence over an arbitrary base.
  Book target: Theorem 7.7.8.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def straighteningUnstraighteningEquiv (U : SCat) (u : UniverseWitness U) (B : SCat) :
    CatEquiv (cocartesianFibrationsOverCat U u B) (funCat B U) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter7

  /-- Straightening sends a small cocartesian fibration to its classifying functor.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def straighteningClassifyingFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor (cocartesianFibrationsOverCat U u B) (funCat B U) :=
    fun U u B => catEquivForward (cocartesianFibrationsOverCat U u B) (funCat B U)
      (straighteningUnstraighteningEquiv U u B)
  /-- Unstraightening sends a classifying functor to its pullback fibration.
  Book context:Chapter 7
  of the SCT book.
  -/
  lf_def unstraighteningClassifyingFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor (funCat B U) (cocartesianFibrationsOverCat U u B) :=
    fun U u B => catEquivBackward (cocartesianFibrationsOverCat U u B) (funCat B U)
      (straighteningUnstraighteningEquiv U u B)
  /-- Category of small left fibrations over a base, represented by cocartesian fibrations
  classified in `Grpd`.  Book context: Chapter 7 of the SCT book.
  -/
  lf_def leftFibrationsOverCat : (U : SCat) ⇒ UniverseWitness U ⇒ (B : SCat) ⇒ SCat :=
    fun U u B => cocartesianFibrationsOverCat U u B
  /-- Left fibrations over `B` are classified by maps into `Grpd`.  Book context: Chapter 7 of the
  SCT book.
  -/
  lf_def leftFibrationStraighteningEquiv : (B : SCat) ⇒
      CatEquiv (leftFibrationsOverCat groupoidUniverse groupoidUniverseWitness B)
        (funCat B groupoidUniverse) :=
    fun B => straighteningUnstraighteningEquiv groupoidUniverse groupoidUniverseWitness B
  /-- Constructive regularity closure data generated from a universe.
  Book context:Chapter 7 of the
  SCT book.
  -/
  syntax_sort ConstructiveRegularUniverseWitness (U : SCat) (u : UniverseWitness U) : Type u
