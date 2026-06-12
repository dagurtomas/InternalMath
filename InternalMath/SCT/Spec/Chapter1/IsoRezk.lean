/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter3.FullSubcategories

/-!
# Chapter 1 Rezk axiom and the category of isomorphisms

This file builds the category `Iso(C)` of invertible interval-shaped morphisms and records the Rezk
axiom.

Book guide, paraphrasing the May 2026 draft:

- Axiom F says every synthetic category `C` is equivalent to the category `Iso(C)` of isomorphisms
  in `C`.
- The object collection for `Iso(C)` is `invertibleMorphismObjects`; its membership directions are
  `invertibleMorphismObjectIntro` and `invertibleMorphismObjectElim`.
- `isoCat` is the full subcategory of `Fun([1], C)` selected by this object collection.
- `isoProjection` and `isoProjectionEmbedding` are the projection to the arrow category and its
  subcategory witness.
- `rezkEquiv` is the Axiom F equivalence `C ≃ Iso(C)`. The derived names
  `identityIsoFunctor`, `isoProjectionFunctor`, `rezkUnit`, and `rezkCounit` are its projections.
-/

@[expose] public section

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Membership of an arrow object in the object collection of invertible arrows. -/
  syntax_abbrev InvertibleMorphismObjectMember {C : SCat}
    (P : ObjectCollection (funCat intervalCat C)) (f : Functor intervalCat C) :=
      ObjectCollectionMember (funCat intervalCat C) P (functorObject intervalCat C f)
  /-- Comprehension package for invertible arrows in `Fun([1], C)`.
  Book target: Definition 1.8.2, building `Iso(C)` from explicit invertible-arrow data. -/
  lf_opaque invertibleMorphismObjectPackage (C : SCat) :
    Σ P : ObjectCollection (funCat intervalCat C),
      (f : Functor intervalCat C) →
        Σ intro : InvertibleMorphism C f → InvertibleMorphismObjectMember C P f,
          InvertibleMorphismObjectMember C P f → InvertibleMorphism C f
  /-- Object collection of invertible arrows in `Fun([1], C)`. -/
  lf_def invertibleMorphismObjects : (C : SCat) ⇒ ObjectCollection (funCat intervalCat C) :=
    fun C => π₁ (invertibleMorphismObjectPackage C)
  /-- Invertible-arrow data gives membership in the invertible-arrow object collection. -/
  lf_def invertibleMorphismObjectIntro : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      InvertibleMorphism C f → InvertibleMorphismObjectMember C (invertibleMorphismObjects C) f :=
    fun C f h => π₁ (π₂ (invertibleMorphismObjectPackage C) f) h
  /-- Membership in the invertible-arrow object collection gives invertible-arrow data. -/
  lf_def invertibleMorphismObjectElim : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      InvertibleMorphismObjectMember C (invertibleMorphismObjects C) f → InvertibleMorphism C f :=
    fun C f h => π₂ (π₂ (invertibleMorphismObjectPackage C) f) h

  /-- Category of isomorphisms in `C`, constructed as the full subcategory of the arrow category
  spanned by invertible arrows.  Book target: Definition 1.8.2.
  -/
  lf_def isoCat : SCat ⇒ SCat :=
    fun C => fullSubcategory (funCat intervalCat C) (invertibleMorphismObjects C)
  /-- Projection from an isomorphism to its underlying arrow; Definition 1.8.2. -/
  lf_def isoProjection : (C : SCat) ⇒ Functor (isoCat C) (funCat intervalCat C) :=
    fun C => fullSubcategoryIncl (funCat intervalCat C) (invertibleMorphismObjects C)
  /-- The projection `Iso(C) → Fun([1],C)` is an embedding, by the full-subcategory witness. -/
  lf_def isoProjectionEmbedding : (C : SCat) ⇒
      Embedding (isoCat C) (funCat intervalCat C) (isoProjection C) :=
    fun C => subcategoryWitnessEmbedding (isoCat C) (funCat intervalCat C) (isoProjection C)
      (fullSubcategoryInclWitness (funCat intervalCat C) (invertibleMorphismObjects C))
namespace SCT

/- The canonical identity-isomorphism functor is admitted as visible construction debt until the
   full-subcategory lift from identity arrows is available. -/
internal_defs where
  /-- Identity-isomorphism functor into the isomorphism category. -/
  def identityIsoFunctor (C : SCat) : Functor C (isoCat C) := sorry

end SCT

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Projection from isomorphisms back to their source objects. -/
  lf_def isoProjectionFunctor : (C : SCat) ⇒ Functor (isoCat C) C :=
    fun C => compFunctor (isoCat C) (funCat intervalCat C) C (isoProjection C) (sourceFunctor C)
  /-- Rezk completeness data pinned to the canonical identity-isomorphism functor. -/
  syntax_abbrev RezkEquivalenceWitness (C : SCat) := Σ unit : NatIso C C
        (compFunctor C (isoCat C) C (identityIsoFunctor C) (isoProjectionFunctor C))
        (idFunctor C),
      NatIso (isoCat C) (isoCat C)
        (compFunctor (isoCat C) C (isoCat C)
          (isoProjectionFunctor C) (identityIsoFunctor C))
        (idFunctor (isoCat C))
  /-- Axiom F as equivalence data for the named Rezk comparison functor. -/
  lf_opaque rezkEquivalenceWitness (C : SCat) : RezkEquivalenceWitness C
  /-- Packaged Rezk completeness equivalence; Axiom F. -/
  lf_def rezkEquiv : (C : SCat) ⇒ CatEquiv C (isoCat C) :=
    fun C => catEquivOfData C (isoCat C) (identityIsoFunctor C) (isoProjectionFunctor C)
      (π₁ (rezkEquivalenceWitness C)) (π₂ (rezkEquivalenceWitness C))
  /-- Unit for the Rezk equivalence; projection from the pinned Axiom F package. -/
  lf_def rezkUnit : (C : SCat) ⇒
      NatIso (compFunctor C (isoCat C) C (identityIsoFunctor C) (isoProjectionFunctor C))
        (idFunctor C) :=
    fun C => π₁ (rezkEquivalenceWitness C)
  /-- Counit for the Rezk equivalence; projection from the pinned Axiom F package. -/
  lf_def rezkCounit : (C : SCat) ⇒
      NatIso (isoCat C) (isoCat C)
        (compFunctor (isoCat C) C (isoCat C)
          (isoProjectionFunctor C) (identityIsoFunctor C))
        (idFunctor (isoCat C)) :=
    fun C => π₂ (rezkEquivalenceWitness C)
