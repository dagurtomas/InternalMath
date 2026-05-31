/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter3.Subcategories

@[expose] public section

extend_type_theory SCT where

  model_section Chapter3

  /-- Membership data for an arrow whose endpoints lie in the chosen object collection. -/
  syntax_abbrev EndpointRestrictedMorphismData (C : SCat) (P : ObjectCollection C)
    (f : Functor intervalCat C) :=
    Σ source_mem : ObjectCollectionMember C P (sourceObj C f),
      ObjectCollectionMember C P (targetObj C f)
  /-- Membership of an interval-shaped morphism in a morphism collection. -/
  syntax_abbrev MorphismCollectionMember (C : SCat) (W : MorphismCollection C)
    (f : Functor intervalCat C) :=
    PreservesMorphismCollection intervalCat C W f
  /-- Source-shaped endpoint-restricted morphism package used to build full subcategories from
  Axiom H.  It contains the collection of arrows whose source and target lie in the chosen object
  collection, identity and composition closure evidence, and the two directions of the endpoint
  membership specification.
  Book target: Definition 3.1.6 and the full-subcategory construction from Axiom H. -/
  lf_opaque fullSubcategoryMorphismComprehensionPackage (C : SCat) (P : ObjectCollection C) :
    Σ W : MorphismCollection C,
      Σ ids : containsIdentities C W,
        Σ comp : closedUnderComposition C W,
          (f : Functor intervalCat C) →
            Σ intro : EndpointRestrictedMorphismData C P f → MorphismCollectionMember C W f,
              MorphismCollectionMember C W f → EndpointRestrictedMorphismData C P f
  /-- Endpoint data determines membership in the endpoint-restricted morphism collection. -/
  lf_def fullSubcategoryMorphismMemberIntro : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      (f : Functor intervalCat C) ⇒ EndpointRestrictedMorphismData C P f →
        MorphismCollectionMember C (fst (fullSubcategoryMorphismComprehensionPackage C P)) f :=
    fun C P f h => fst (snd (snd (snd (fullSubcategoryMorphismComprehensionPackage C P))) f) h
  /-- Membership in the endpoint-restricted collection recovers endpoint data. -/
  lf_def fullSubcategoryMorphismMemberElim : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      (f : Functor intervalCat C) ⇒
        MorphismCollectionMember C (fst (fullSubcategoryMorphismComprehensionPackage C P)) f →
          EndpointRestrictedMorphismData C P f :=
    fun C P f h => snd (snd (snd (snd (fullSubcategoryMorphismComprehensionPackage C P))) f) h

  /-- Morphism collection of arrows whose endpoints lie in the chosen object collection. -/
  lf_def fullSubcategoryMorphismCollection : (C : SCat) ⇒ ObjectCollection C ⇒
      MorphismCollection C :=
    fun C P => fst (fullSubcategoryMorphismComprehensionPackage C P)
  /-- Endpoint-restricted morphisms contain identities. -/
  lf_def fullSubcategoryMorphismContainsIdentities : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      containsIdentities C (fullSubcategoryMorphismCollection C P) :=
    fun C P => fst (snd (fullSubcategoryMorphismComprehensionPackage C P))
  /-- Endpoint-restricted morphisms are closed under composition. -/
  lf_def fullSubcategoryMorphismClosed : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      closedUnderComposition C (fullSubcategoryMorphismCollection C P) :=
    fun C P => fst (snd (snd (fullSubcategoryMorphismComprehensionPackage C P)))
  /-- Full subcategory determined by an object collection; Definition 3.1.6. -/
  lf_def fullSubcategory : (C : SCat) ⇒ ObjectCollection C ⇒ SCat :=
    fun C P => subcategory C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P)
  /-- Inclusion of a full subcategory; Definition 3.1.6. -/
  lf_def fullSubcategoryIncl : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      Functor (fullSubcategory C P) C :=
    fun C P => subcategoryIncl C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P)
  /-- The full-subcategory inclusion is a subcategory, by Corollary 3.1.11. -/
  lf_def fullSubcategoryInclWitness : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      SubcategoryWitness (fullSubcategory C P) C (fullSubcategoryIncl C P) :=
    fun C P => subcategoryInclWitness C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P)

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- The core of a full subcategory is the specified object collection.
  Book target: §3.1, full subcategories determined by object collections.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  -/
  def fullSubcategoryCoreEquiv (C : SCat) (P : ObjectCollection C) :
    CatEquiv (coreCat (fullSubcategory C P)) (objectCollectionCat C P) := sorry
  /-- The full subcategory spanned by all objects is equivalent to the ambient category.
  Book target: §3.1, full subcategories determined by object collections.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  -/
  def fullSubcategoryAllObjectsEquiv (C : SCat) (P : ObjectCollection C)
    (hAll : CatEquiv (objectCollectionCat C P) (coreCat C)) :
      CatEquiv (fullSubcategory C P) C := sorry

end SCT
