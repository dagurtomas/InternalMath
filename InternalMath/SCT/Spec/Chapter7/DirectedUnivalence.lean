/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.Straightening

/-!
# Chapter 7 directed univalence

This file records the directed-univalence comparison between transformations of classifying maps
and cocartesian functors.

Book guide, paraphrasing the May 2026 draft:

- Directed univalence says that, for the universal cocartesian fibration, transformations between
  classifying maps correspond to cocartesian functors between the classified fibrations.
- `classifiedCocartesianFunctorUnderlying` forgets a cocartesian functor to its underlying functor.
- The comparison equivalence is `directedUnivalenceMappingEquiv`.
- The declarations `directedUnivalenceCocartesianObject`, `directedUnivalenceFunctor`,
  `directedUnivalenceToTransformation`, and `directedUnivalenceFunctorCocartesian` expose the two
  directions and the cocartesian witness.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter7

  /-- Inclusion of classified cocartesian functors into the ordinary functor category.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def classifiedCocartesianFunctorUnderlying : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
        Functor (classifiedCocartesianFunctorCat U u B f g)
          (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)) :=
    fun U u B f g => compFunctor (classifiedCocartesianFunctorCat U u B f g)
      (functorOverBaseCat B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedProjection U u B g))
      (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
      (cocartesianFunctorCatIncl B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedFibration U u B f)
        (classifiedCocartesian U u B f)
        (classifiedProjection U u B g) (classifiedFibration U u B g)
        (classifiedCocartesian U u B g))
      (functorOverBaseIncl B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedProjection U u B g))

extend_type_theory SCT where

  model_section Chapter7

  /-- Directed-univalence equivalence between classifying transformations and cocartesian functors;
  Axiom N/Definition 7.3.10 data. -/
  lf_opaque directedUnivalenceMappingEquiv (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U) :
    CatEquiv (natTransCat B U f g) (classifiedCocartesianFunctorCat U u B f g)

extend_type_theory SCT where

  model_section Chapter7

  /-- Object of the cocartesian-functor category produced from a classifying transformation.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def directedUnivalenceCocartesianObject : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
        (universeFibration U u) (universeCocartesian U u)) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
      ClassifyingTransformation B U f g ⇒ Obj (classifiedCocartesianFunctorCat U u B f g) :=
    fun U u du B f g α => compFunctor terminalCat (natTransCat B U f g)
      (classifiedCocartesianFunctorCat U u B f g) (natTransObject B U f g α)
      (catEquivForward (natTransCat B U f g) (classifiedCocartesianFunctorCat U u B f g)
        (directedUnivalenceMappingEquiv U u du B f g))
  /-- Underlying functor produced from a classifying transformation by directed univalence. -/
  lf_def directedUnivalenceFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
        (universeFibration U u) (universeCocartesian U u)) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
      ClassifyingTransformation B U f g ⇒
        Functor (classifiedTotalCat U u B f) (classifiedTotalCat U u B g) :=
    fun U u du B f g α => functorFromObject (classifiedTotalCat U u B f)
      (classifiedTotalCat U u B g)
      (compFunctor terminalCat (classifiedCocartesianFunctorCat U u B f g)
        (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
        (directedUnivalenceCocartesianObject U u du B f g α)
        (classifiedCocartesianFunctorUnderlying U u B f g))

  /-- Smallness of a category relative to a universe; §7.3.1 and §7.4. -/
  syntax_sort SmallWitness (U : SCat) (C : SCat) : Type u

extend_type_theory SCT where

  model_section Chapter7

  /-- The functor produced by directed univalence is cocartesian; Axiom N/Definition 7.3.10 data. -/
  lf_opaque directedUnivalenceFunctorCocartesian (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U)
    (α : ClassifyingTransformation B U f g) :
    CocartesianFunctorWitness (classifiedTotalCat U u B f) B (classifiedProjection U u B f)
      (classifiedFibration U u B f) (classifiedCocartesian U u B f)
      (classifiedTotalCat U u B g) (classifiedProjection U u B g)
      (classifiedFibration U u B g) (classifiedCocartesian U u B g)
      (directedUnivalenceFunctor U u du B f g α)
  /-- Directed univalence sends cocartesian functors back to transformations; Axiom N/Definition
  7.3.10 data. -/
  lf_opaque directedUnivalenceToTransformation (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U)
    (F : Functor (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
    (hF : CocartesianFunctorWitness (classifiedTotalCat U u B f) B
      (classifiedProjection U u B f) (classifiedFibration U u B f)
      (classifiedCocartesian U u B f) (classifiedTotalCat U u B g)
      (classifiedProjection U u B g) (classifiedFibration U u B g)
      (classifiedCocartesian U u B g) F) : ClassifyingTransformation B U f g
