/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter1.IsoRezk

/-!
# Chapter 3 lifts through subcategories and full subcategories

This file exposes the universal property of the Axiom H subcategory and its full-subcategory
specialization.

Book guide, paraphrasing the May 2026 draft:

- Axiom H gives a universal lift for any functor preserving the selected morphism collection. The
  projections are `subcategoryLift`, `subcategoryLiftBeta`, and `subcategoryLiftUniq`.
- For full subcategories, `fullSubcategoryInclLands` should say that the inclusion lands in the
  chosen object collection.
- A functor landing in an object collection should preserve the endpoint-restricted morphism
  collection; this is the admitted theorem `landsInObjectCollectionPreservesFull`.
- `Chapter3/Localization.lean` uses these declarations to define lifts through full subcategories.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter3

  /-- Universal lift through a subcategory; Axiom H. -/
  lf_def subcategoryLift : (D : SCat) ⇒ (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (ids : containsIdentities C W) ⇒ (comp : closedUnderComposition C W) ⇒
      (F : Functor D C) ⇒ PreservesMorphismCollection D C W F ⇒
        Functor D (subcategory C W ids comp) :=
    fun D C W ids comp F h =>
      fst ((snd (snd (snd (subcategoryPackage C W ids comp)))) D F h)
  /-- β comparison for the subcategory lift; Axiom H. -/
  lf_def subcategoryLiftBeta : (D : SCat) ⇒ (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (ids : containsIdentities C W) ⇒ (comp : closedUnderComposition C W) ⇒
      (F : Functor D C) ⇒ (h : PreservesMorphismCollection D C W F) ⇒
        NatIso D C
          (compFunctor D (subcategory C W ids comp) C
            (subcategoryLift D C W ids comp F h) (subcategoryIncl C W ids comp))
          F :=
    fun D C W ids comp F h =>
      fst (snd ((snd (snd (snd (subcategoryPackage C W ids comp)))) D F h))
  /-- Uniqueness of subcategory lifts over `C`; Axiom H. -/
  lf_def subcategoryLiftUniq : (D : SCat) ⇒ (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (ids : containsIdentities C W) ⇒ (comp : closedUnderComposition C W) ⇒
      (F : Functor D C) ⇒ (h : PreservesMorphismCollection D C W F) ⇒
      (K : Functor D (subcategory C W ids comp)) ⇒
      (β : NatIso D C
        (compFunctor D (subcategory C W ids comp) C K (subcategoryIncl C W ids comp)) F) ⇒
        NatIso D (subcategory C W ids comp) K (subcategoryLift D C W ids comp F h) :=
    fun D C W ids comp F h K β =>
      snd (snd ((snd (snd (snd (subcategoryPackage C W ids comp)))) D F h)) K β
namespace SCT

/- Theorem-shaped declaration admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- The full-subcategory inclusion lands in its defining object collection.
  Book target: §3.1, full subcategories determined by object collections.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  -/
  def fullSubcategoryInclLands (C : SCat) (P : ObjectCollection C) :
    LandsInObjectCollection (fullSubcategory C P) C P (fullSubcategoryIncl C P) := sorry

end SCT

namespace SCT

/- Landing in an object collection implies preservation of the endpoint-restricted collection. -/
internal_defs where
  /-- A functor landing in the object collection preserves the endpoint-restricted morphism
  collection used to build the full subcategory.
  Book target: Definition 3.1.6 and the universal property of full subcategories.
  Status: temporary sorry-admitted theorem-shaped evidence; not a model-provider field. -/
  def landsInObjectCollectionPreservesFull (D : SCat) (C : SCat) (P : ObjectCollection C)
    (F : Functor D C) (h : LandsInObjectCollection D C P F) :
    PreservesMorphismCollection D C (fullSubcategoryMorphismCollection C P) F := sorry

end SCT
