/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter6.FundamentalTheorem

/-!
# Chapter 7 cocartesian functors and universe vocabulary

This file starts the Chapter 7 universe and directed-univalence layer. Axiom labels use the body
labels from the May 2026 draft: Axiom M is exponentiability of cartesian/cocartesian fibrations, and
Axiom N is the directed-univalence/classification axiom.

Book guide, paraphrasing the May 2026 draft:

- `UniverseWitness` names a universe of small categories; its fibration data appears in
  `Chapter7/Straightening.lean`.
- `DirectedUnivalenceWitness` is the directed-univalence structure for a cocartesian fibration.
- `ClassifyingTransformation` is the SCT proxy for transformations between classifying maps.
- `functorOverBaseCat` and `functorOverBaseIncl` describe functors over a fixed base.
- The universe fibration starts with `universeTotalCat`; later files add its projection,
  fibration, cocartesian structure, and directed-univalence witness.
- Definition 7.1.10 forms the category of cocartesian functors over a base. The package
  `cocartesianFunctorCategoryPackage` exposes `cocartesianFunctorCat` and
  `cocartesianFunctorCatIncl`, while `isCocartesianFunctorCat` and
  `cocartesianFunctorCatSubcategory` remain admitted construction/proof debt.
-/

@[expose] public section

/-- Chapter 7: universes and directed univalence; Axioms M and N. -/
extend_type_theory SCT where

  model_section Chapter7


  /-- Directed-univalence witness for a cocartesian fibration; Axiom N/Definition 7.3.10. -/
  syntax_sort DirectedUnivalenceWitness {U : SCat} {Udot : SCat} (p : Functor Udot U)
    (fib : Fibration Udot U p) (cocart : CocartesianFibrationWitness Udot U p fib) : Type u
  /-- Classifying transformations are natural transformations between classifiers, as in Chapter 7
  of the SCT book.
  -/
  syntax_abbrev ClassifyingTransformation {B : SCat} {U : SCat}
    (f : Functor B U) (g : Functor B U) := NatTrans f g
  /-- Universe-of-categories package; Chapter 7 universe structure. -/
  syntax_sort UniverseWitness (U : SCat) : Type u
  /-- Category of functors over a fixed base, as the fiber of postcomposition with the target
  projection.  Book context: Chapter 7 of the SCT book.
  -/
  lf_def functorOverBaseCat : (B : SCat) ⇒ (E : SCat) ⇒ (F : SCat) ⇒
      Functor E B ⇒ Functor F B ⇒ SCat :=
    fun B E F p q => pullbackCat (funCat E F) terminalCat (funCat E B)
      (postcompFunctor E F B q) (functorObject E B p)
  /-- Inclusion from functors-over-`B` to ordinary functors.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def functorOverBaseIncl : (B : SCat) ⇒ (E : SCat) ⇒ (F : SCat) ⇒
      (p : Functor E B) ⇒ (q : Functor F B) ⇒
        Functor (functorOverBaseCat B E F p q) (funCat E F) :=
    fun B E F p q => pullbackPr1 (funCat E F) terminalCat (funCat E B)
      (postcompFunctor E F B q) (functorObject E B p)
  /-- Total category of the universe fibration; Chapter 7 universe structure. -/
  lf_opaque universeTotalCat (U : SCat) (u : UniverseWitness U) : SCat

namespace SCT

internal_defs where
  /-- Category of proof objects that a functor over `B` is cocartesian.
  Book target: Construction 7.1.2.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct it from functors over the base and Beck-Chevalley proof
  objects. -/
  def isCocartesianFunctorCat (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p)
    (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q)
    (cocartq : CocartesianFibrationWitness F B q fibq) : SCat := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter7

  /-- Package for `CoCart_B(E,F)` and its inclusion into functors over the base;
  Definition 7.1.10.  The subcategory witness is lint-visible theorem debt. -/
  lf_opaque cocartesianFunctorCategoryPackage (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p)
    (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q)
    (cocartq : CocartesianFibrationWitness F B q fibq) :
    Σ CoCart : SCat, Functor CoCart (functorOverBaseCat B E F p q)
  /-- Non-full subcategory `CoCart_B(E,F)` of cocartesian functors; Definition 7.1.10. -/
  lf_def cocartesianFunctorCat : (B : SCat) ⇒ (E : SCat) ⇒ (F : SCat) ⇒
      (p : Functor E B) ⇒ (fibp : Fibration E B p) ⇒
      (cocartp : CocartesianFibrationWitness E B p fibp) ⇒
      (q : Functor F B) ⇒ (fibq : Fibration F B q) ⇒
      (cocartq : CocartesianFibrationWitness F B q fibq) ⇒ SCat :=
    fun B E F p fibp cocartp q fibq cocartq =>
      fst (cocartesianFunctorCategoryPackage B E F p fibp cocartp q fibq cocartq)
  /-- Inclusion `CoCart_B(E,F) → Fun_B(E,F)`; Definition 7.1.10. -/
  lf_def cocartesianFunctorCatIncl : (B : SCat) ⇒ (E : SCat) ⇒ (F : SCat) ⇒
      (p : Functor E B) ⇒ (fibp : Fibration E B p) ⇒
      (cocartp : CocartesianFibrationWitness E B p fibp) ⇒
      (q : Functor F B) ⇒ (fibq : Fibration F B q) ⇒
      (cocartq : CocartesianFibrationWitness F B q fibq) ⇒
      Functor (cocartesianFunctorCat B E F p fibp cocartp q fibq cocartq)
        (functorOverBaseCat B E F p q) :=
    fun B E F p fibp cocartp q fibq cocartq =>
      snd (cocartesianFunctorCategoryPackage B E F p fibp cocartp q fibq cocartq)

namespace SCT

internal_defs where
  /-- `CoCart_B(E,F)` is the subcategory selected by the Beck-Chevalley condition.
  Book target: Definition 7.1.10.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove the chosen cocartesian-functor category and inclusion satisfy
  Definition 7.1.10. -/
  def cocartesianFunctorCatSubcategory (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p)
    (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q)
    (cocartq : CocartesianFibrationWitness F B q fibq) :
    SubcategoryWitness (cocartesianFunctorCat B E F p fibp cocartp q fibq cocartq)
      (functorOverBaseCat B E F p q)
      (cocartesianFunctorCatIncl B E F p fibp cocartp q fibq cocartq) := sorry

end SCT
