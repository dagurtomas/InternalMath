/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter5.LimitsColimits

/-!
# Chapter 6 definitions for the Fundamental Theorem

This file introduces the three hypotheses used in the Fundamental Theorem of category theory.

Book guide, paraphrasing the May 2026 draft:

- Fully faithful functors are characterized by a pullback condition comparing arrows in `C` with
  arrows in `D` over pairs of objects. The declarations `arrowEndpointFunctor`, `objectPairFunctor`,
  and `arrowMapFunctor` build this comparison, and `FullyFaithful` packages it as a pullback square.
- Conservative functors are characterized by a pullback condition on cores; this is `Conservative`.
- Strongly surjective functors have a section of the induced functor on cores, up to natural
  isomorphism; this is `StronglySurjective`.
- `fullyFaithfulHomEquiv` is theorem debt saying the fully faithful criterion gives equivalences on
  fixed-endpoint hom categories.
-/

@[expose] public section

/-- Chapter 6: the Fundamental Theorem of category theory. -/
extend_type_theory SCT where

  model_section Chapter6


  /-- Endpoint-pair functor of the arrow category.  Book context: Chapter 6 of the SCT book. -/
  lf_def arrowEndpointFunctor : (C : SCat) ⇒ Functor (funCat intervalCat C) (prodCat C C) :=
    fun C => prodPair (funCat intervalCat C) C C (sourceFunctor C) (targetFunctor C)
  /-- Object-pair action of a functor.  Book context: Chapter 6 of the SCT book. -/
  lf_def objectPairFunctor : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒
      Functor (prodCat C C) (prodCat D D) :=
    fun C D F => prodPair (prodCat C C) D D
      (compFunctor (prodCat C C) C D (prodPr1 C C) F)
      (compFunctor (prodCat C C) C D (prodPr2 C C) F)
  /-- Fully faithful functors, represented by the endpoint-pullback arrow criterion.  Book context:
  Chapter 6 of the SCT book.
  -/
  syntax_abbrev FullyFaithful {C : SCat} {D : SCat} (F : Functor C D) :=
    CatEquiv (funCat intervalCat C)
      (pullbackCat (prodCat C C) (funCat intervalCat D) (prodCat D D)
        (objectPairFunctor C D F) (arrowEndpointFunctor D))
  /-- Conservative functors, represented by the core-pullback criterion.  Book context: Chapter 6 of
  the SCT book.
  -/
  syntax_abbrev Conservative {C : SCat} {D : SCat} (F : Functor C D) :=
    PullbackSquare (coreCat C) C (coreCat D) D (coreIncl C) (coreFunctor C D F) F (coreIncl D)
  /-- Strongly-surjective functors, represented by a section of the induced map on cores;
  Definition 6.3.1. -/
  syntax_abbrev StronglySurjective {C : SCat} {D : SCat} (F : Functor C D) :=
    Σ s : Functor (coreCat D) (coreCat C),
      NatIso (coreCat D) (coreCat D)
        (compFunctor (coreCat D) (coreCat C) (coreCat D) s (coreFunctor C D F))
        (idFunctor (coreCat D))

namespace SCT

/- Theorem-shaped declaration admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Fully faithful functors induce equivalences on object-hom categories; Definition 6.1.1.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: derive this fiberwise equivalence from the endpoint-pullback
  definition of `FullyFaithful`.
  -/
  def fullyFaithfulHomEquiv (C : SCat) (D : SCat) (F : Functor C D)
    (ff : FullyFaithful C D F) (x : Obj C) (y : Obj C) :
    CatEquiv (objectHomCat C x y)
      (objectHomCat D (compFunctor terminalCat C D x F)
        (compFunctor terminalCat C D y F)) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter6

  /-- Fully faithful functors induce the source pullback equivalence on arrows.  Book context:
  Chapter 6 of the SCT book.
  -/
  lf_def fullyFaithfulArrowMapEquiv : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      FullyFaithful C D F ⇒
        CatEquiv (funCat intervalCat C)
          (pullbackCat (prodCat C C) (funCat intervalCat D) (prodCat D D)
            (objectPairFunctor C D F) (arrowEndpointFunctor D)) :=
    fun C D F ff => ff
  /-- Postcomposition preserves the source/target endpoint map on arrow categories.  This is
  functor-category endpoint β-data used to construct the Chapter 6 arrow comparison. -/
  lf_opaque postcompEndpointFunctorCompat (C : SCat) (D : SCat) (F : Functor C D) :
    NatIso (funCat intervalCat C) (prodCat D D)
      (compFunctor (funCat intervalCat C) (prodCat C C) (prodCat D D)
        (arrowEndpointFunctor C) (objectPairFunctor C D F))
      (compFunctor (funCat intervalCat C) (funCat intervalCat D) (prodCat D D)
        (postcompFunctor intervalCat C D F) (arrowEndpointFunctor D))
  /-- Arrow-map comparison into the endpoint pullback.  Book target: §6.2, arrow-map
  characterization of fully faithful functors. -/
  lf_def arrowMapFunctor : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      Functor (funCat intervalCat C)
        (pullbackCat (prodCat C C) (funCat intervalCat D) (prodCat D D)
          (objectPairFunctor C D F) (arrowEndpointFunctor D)) :=
    fun C D F => pullbackLift (funCat intervalCat C)
      (prodCat C C) (funCat intervalCat D) (prodCat D D)
      (objectPairFunctor C D F) (arrowEndpointFunctor D)
      (arrowEndpointFunctor C) (postcompFunctor intervalCat C D F)
      (postcompEndpointFunctorCompat C D F)

extend_type_theory SCT where

  model_section Chapter6

  /-- The core square of a conservative functor is a pullback; this is the chosen representation.
  Book context: Chapter 6 of the SCT book.
  -/
  lf_def conservativeCorePullback : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      Conservative C D F ⇒ PullbackSquare (coreCat C) C (coreCat D) D
        (coreIncl C) (coreFunctor C D F) F (coreIncl D) :=
    fun C D F cons => cons
