/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.CocartesianFunctors

/-!
# Chapter 7 universe fibrations and straightening over `[1]`

This file records the split data for the universe fibration and the special straightening
construction over `[1]`.

Book guide, paraphrasing the May 2026 draft:

- Axiom N supplies, for a universe `U`, a universal cocartesian fibration. The split data is
  `universeProjection`, `universeFibration`, `universeCocartesian`, and
  `universeDirectedUnivalence`.
- Pulling the universe fibration back along a classifying map gives a classified total category,
  projection, fibration witness, and cocartesian witness. These are `classifiedTotalCat`,
  `classifiedProjection`, `classifiedFibration`, and `classifiedCocartesian`.
- The Section 7.7 unstraightening aliases are `unstraighteningTotal`,
  `unstraighteningProjection`, `unstraighteningFibration`, and `unstraighteningCocartesian`.
- For a cocartesian fibration over `[1] × B`, the straightening source and target are built by
  pulling back along the endpoints of `[1]`. The admitted straightening data is
  `straighteningFunctor` and `straighteningFunctorCocartesian`.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter7

  /-- Projection of the universe fibration; Axiom N. -/
  lf_opaque universeProjection (U : SCat) (u : UniverseWitness U) :
    Functor (universeTotalCat U u) U
  /-- Fibration structure on the universe projection; Axiom N. -/
  lf_opaque universeFibration (U : SCat) (u : UniverseWitness U) :
    Fibration (universeTotalCat U u) U (universeProjection U u)
  /-- Cocartesian structure on the universe projection; Axiom N. -/
  lf_opaque universeCocartesian (U : SCat) (u : UniverseWitness U) :
    CocartesianFibrationWitness (universeTotalCat U u) U (universeProjection U u)
      (universeFibration U u)
  /-- Directed univalence of the universe projection; Axiom N. -/
  lf_opaque universeDirectedUnivalence (U : SCat) (u : UniverseWitness U) :
    DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u)
  /-- Total category classified by a map into a universe; Axiom N. -/
  lf_def classifiedTotalCat : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ SCat :=
    fun U u B f => pullbackCat B (universeTotalCat U u) U f (universeProjection U u)
  /-- Projection of a classified fibration; Axiom N. -/
  lf_def classifiedProjection : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ Functor (classifiedTotalCat U u B f) B :=
    fun U u B f => pullbackPr1 B (universeTotalCat U u) U f (universeProjection U u)
  /-- Fibration classified by a universe map; Axiom N. -/
  lf_def classifiedFibration : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        Fibration (classifiedTotalCat U u B f) B (classifiedProjection U u B f) :=
    fun U u B f => baseChangeFibration (universeTotalCat U u) U
      (universeProjection U u) (universeFibration U u) B f
  /-- Cocartesian structure classified by a universe map; Axiom N. -/
  lf_def classifiedCocartesian : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        CocartesianFibrationWitness (classifiedTotalCat U u B f) B
          (classifiedProjection U u B f) (classifiedFibration U u B f) :=
    fun U u B f => baseChangeCocartesian (universeTotalCat U u) U
      (universeProjection U u) (universeFibration U u) (universeCocartesian U u) B f
  /-- Unstraightening total category for a classifying map; Section 7.7.  Book context: Chapter 7 of
  the SCT book.
  -/
  lf_def unstraighteningTotal : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ SCat :=
    fun U u B f => classifiedTotalCat U u B f
  /-- Unstraightening projection for a classifying map; Section 7.7.  Book context: Chapter 7 of the
  SCT book.
  -/
  lf_def unstraighteningProjection : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ Functor (unstraighteningTotal U u B f) B :=
    fun U u B f => classifiedProjection U u B f
  /-- Unstraightening fibration structure for a classifying map; Section 7.7.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def unstraighteningFibration : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        Fibration (unstraighteningTotal U u B f) B (unstraighteningProjection U u B f) :=
    fun U u B f => classifiedFibration U u B f
  /-- Unstraightening cocartesian structure for a classifying map; Section 7.7.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def unstraighteningCocartesian : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        CocartesianFibrationWitness (unstraighteningTotal U u B f) B
          (unstraighteningProjection U u B f) (unstraighteningFibration U u B f) :=
    fun U u B f => classifiedCocartesian U u B f

  /-- Inclusion of the zero slice `B → [1] × B`; Section 7.2.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def zeroBaseInclusion : (B : SCat) ⇒ Functor B (prodCat intervalCat B) :=
    fun B => prodPair B intervalCat B
      (compFunctor B terminalCat intervalCat (terminalProjection B) intervalZero)
      (idFunctor B)
  /-- Inclusion of the one slice `B → [1] × B`; Section 7.2.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def oneBaseInclusion : (B : SCat) ⇒ Functor B (prodCat intervalCat B) :=
    fun B => prodPair B intervalCat B
      (compFunctor B terminalCat intervalCat (terminalProjection B) intervalOne)
      (idFunctor B)
  /-- Source fiber of a fibration over `[1] × B`; Definition 7.2.3. -/
  lf_def straighteningSourceTotal : (B : SCat) ⇒ (E : SCat) ⇒
      Functor E (prodCat intervalCat B) ⇒ SCat :=
    fun B E p => pullbackCat B E (prodCat intervalCat B) (zeroBaseInclusion B) p
  /-- Target fiber of a fibration over `[1] × B`; Definition 7.2.3. -/
  lf_def straighteningTargetTotal : (B : SCat) ⇒ (E : SCat) ⇒
      Functor E (prodCat intervalCat B) ⇒ SCat :=
    fun B E p => pullbackCat B E (prodCat intervalCat B) (oneBaseInclusion B) p
  /-- Projection of the source fiber over `B`; Definition 7.2.3. -/
  lf_def straighteningSourceProjection : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒
        Functor (straighteningSourceTotal B E p) B :=
    fun B E p => pullbackPr1 B E (prodCat intervalCat B) (zeroBaseInclusion B) p
  /-- Projection of the target fiber over `B`; Definition 7.2.3. -/
  lf_def straighteningTargetProjection : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒
        Functor (straighteningTargetTotal B E p) B :=
    fun B E p => pullbackPr1 B E (prodCat intervalCat B) (oneBaseInclusion B) p
  /-- Source-fiber fibration, by base change; Definition 7.2.3. -/
  lf_def straighteningSourceFibration : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ Fibration E (prodCat intervalCat B) p ⇒
        Fibration (straighteningSourceTotal B E p) B
          (straighteningSourceProjection B E p) :=
    fun B E p fib => baseChangeFibration E (prodCat intervalCat B) p fib B
      (zeroBaseInclusion B)
  /-- Target-fiber fibration, by base change; Definition 7.2.3. -/
  lf_def straighteningTargetFibration : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ Fibration E (prodCat intervalCat B) p ⇒
        Fibration (straighteningTargetTotal B E p) B
          (straighteningTargetProjection B E p) :=
    fun B E p fib => baseChangeFibration E (prodCat intervalCat B) p fib B
      (oneBaseInclusion B)
  /-- Source-fiber cocartesian structure, by base change; Definition 7.2.3. -/
  lf_def straighteningSourceCocartesian : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ (fib : Fibration E (prodCat intervalCat B) p) ⇒
      CocartesianFibrationWitness E (prodCat intervalCat B) p fib ⇒
        CocartesianFibrationWitness (straighteningSourceTotal B E p) B
          (straighteningSourceProjection B E p) (straighteningSourceFibration B E p fib) :=
    fun B E p fib cocart => baseChangeCocartesian E (prodCat intervalCat B) p fib
      cocart B (zeroBaseInclusion B)
  /-- Target-fiber cocartesian structure, by base change; Definition 7.2.3. -/
  lf_def straighteningTargetCocartesian : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ (fib : Fibration E (prodCat intervalCat B) p) ⇒
      CocartesianFibrationWitness E (prodCat intervalCat B) p fib ⇒
        CocartesianFibrationWitness (straighteningTargetTotal B E p) B
          (straighteningTargetProjection B E p) (straighteningTargetFibration B E p fib) :=
    fun B E p fib cocart => baseChangeCocartesian E (prodCat intervalCat B) p fib
      cocart B (oneBaseInclusion B)
  /-- Cocartesian functor category between two classified fibrations.
  Book context:Chapter 7 of the
  SCT book.
  -/
  lf_def classifiedCocartesianFunctorCat : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ Functor B U ⇒ SCat :=
    fun U u B f g => cocartesianFunctorCat B (classifiedTotalCat U u B f)
      (classifiedTotalCat U u B g) (classifiedProjection U u B f) (classifiedFibration U u B f)
      (classifiedCocartesian U u B f) (classifiedProjection U u B g)
      (classifiedFibration U u B g) (classifiedCocartesian U u B g)

namespace SCT

internal_defs where
  /-- Straightening over `[1]`.
  Book target: Construction 7.2.1 and Definition 7.2.3.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the functor from locally cocartesian transport over
  `[1] × B`. -/
  def straighteningFunctor (B : SCat) (E : SCat)
    (p : Functor E (prodCat intervalCat B))
    (fib : Fibration E (prodCat intervalCat B) p)
    (cocart : CocartesianFibrationWitness E (prodCat intervalCat B) p fib) :
    Functor (straighteningSourceTotal B E p) (straighteningTargetTotal B E p) := sorry

  /-- Straightening is a cocartesian functor over the base.
  Book target: Construction 7.2.1/Lemma 7.2.2.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove the straightening functor preserves cocartesian arrows. -/
  def straighteningFunctorCocartesian (B : SCat) (E : SCat)
    (p : Functor E (prodCat intervalCat B))
    (fib : Fibration E (prodCat intervalCat B) p)
    (cocart : CocartesianFibrationWitness E (prodCat intervalCat B) p fib) :
    CocartesianFunctorWitness (straighteningSourceTotal B E p) B
      (straighteningSourceProjection B E p) (straighteningSourceFibration B E p fib)
      (straighteningSourceCocartesian B E p fib cocart) (straighteningTargetTotal B E p)
      (straighteningTargetProjection B E p) (straighteningTargetFibration B E p fib)
      (straighteningTargetCocartesian B E p fib cocart)
      (straighteningFunctor B E p fib cocart) := sorry

end SCT
