/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.DirectedUnivalence

/-!
# Chapter 7 smallness, Axiom M, and regular universes

This file records smallness relative to a universe, exponentiability of fibrations, and the regular
universe closure operations.

Book guide, paraphrasing the May 2026 draft:

- Axiom N classifies small categories and small cocartesian fibrations. The relevant declarations
  include `SmallWitness`, `smallClassifyingMap`, `smallClassifyingEquiv`,
  `SmallCocartesianFibrationWitness`, `smallFibrationClassifyingMap`, and
  `smallFibrationClassifyingEquiv`.
- Definition 7.4.6 names functors with small fibers; this is `SmallFibersWitness`.
- Axiom M says cartesian and cocartesian fibrations are exponentiable. The witness is
  `ExponentiableFibrationWitness`, with constructors `cartesianFibrationExponentiable` and
  `cocartesianFibrationExponentiable`.
- Definition 7.4.5 describes regular universes and closure operations. The declarations include
  `RegularUniverseWitness`, `categoryUniverse`, `categoryUniverseWitness`,
  `categoryUniverseRegular`, and the `catInternal...`, `catClosure...`, and
  `regularUniverse...` fields.
- The dependent-product closure part of regularity is represented by `dependentProductTotal`,
  `dependentProductProjection`, `dependentProductFibration`, and `dependentProductSmall`.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter7

  /-- Classifying map for a small category; Axiom N. -/
  lf_opaque smallClassifyingMap (U : SCat) (u : UniverseWitness U)
    (C : SCat) (hC : SmallWitness U C) : Functor terminalCat U
  /-- Pullback of the universe along the classifier recovers the small category; Axiom N. -/
  lf_opaque smallClassifyingEquiv (U : SCat) (u : UniverseWitness U)
    (C : SCat) (hC : SmallWitness U C) :
    CatEquiv C (classifiedTotalCat U u terminalCat (smallClassifyingMap U u C hC))
  /-- Small cocartesian fibration relative to a universe; Axiom N. -/
  syntax_sort SmallCocartesianFibrationWitness (U : SCat) (E : SCat) (B : SCat)
    (p : Functor E B) (fib : Fibration E B p)
    (cocart : CocartesianFibrationWitness E B p fib) : Type u
  /-- Functor with small fibers relative to a universe; Definition 7.4.6. -/
  syntax_sort SmallFibersWitness (U : SCat) (E : SCat) (B : SCat) (p : Functor E B) : Type u
  /-- Classifying map for a small cocartesian fibration; Axiom N. -/
  lf_opaque smallFibrationClassifyingMap (U : SCat) (u : UniverseWitness U)
    (E : SCat) (B : SCat) (p : Functor E B) (fib : Fibration E B p)
    (cocart : CocartesianFibrationWitness E B p fib)
    (h : SmallCocartesianFibrationWitness U E B p fib cocart) : Functor B U
  /-- The classified pullback recovers a small cocartesian fibration; Axiom N. -/
  lf_opaque smallFibrationClassifyingEquiv (U : SCat) (u : UniverseWitness U)
    (E : SCat) (B : SCat) (p : Functor E B) (fib : Fibration E B p)
    (cocart : CocartesianFibrationWitness E B p fib)
    (h : SmallCocartesianFibrationWitness U E B p fib cocart) :
    CatEquiv E (classifiedTotalCat U u B
      (smallFibrationClassifyingMap U u E B p fib cocart h))
  /-- A regular universe; Axiom N and Definition 7.4.5 (Cat1). -/
  syntax_sort RegularUniverseWitness (U : SCat) (u : UniverseWitness U) : Type u
  /-- Exponentiability witness for cartesian/cocartesian fibrations; Axiom M. -/
  syntax_sort ExponentiableFibrationWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) : Type u
  /-- Cartesian fibrations are exponentiable; Axiom M. -/
  lf_opaque cartesianFibrationExponentiable (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib) :
    ExponentiableFibrationWitness E B p fib
  /-- Cocartesian fibrations are exponentiable; Axiom M. -/
  lf_opaque cocartesianFibrationExponentiable (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    ExponentiableFibrationWitness E B p fib
  /-- Total category of a dependent product of a fibration; Definition 7.4.5 (Cat6). -/
  lf_opaque dependentProductTotal (A : SCat) (B : SCat) (E : SCat)
    (p : Functor E B) (u : Functor A B) : SCat
  /-- Projection of a dependent-product fibration; Definition 7.4.5 (Cat6). -/
  lf_opaque dependentProductProjection (A : SCat) (B : SCat) (E : SCat)
    (p : Functor E B) (u : Functor A B) :
    Functor (dependentProductTotal A B E p u) A
  /-- Fibration structure on a dependent product; Definition 7.4.5 (Cat6). -/
  lf_opaque dependentProductFibration (A : SCat) (B : SCat) (E : SCat)
    (p : Functor E B) (u : Functor A B) (fib : Fibration E B p) :
    Fibration (dependentProductTotal A B E p u) A
      (dependentProductProjection A B E p u)
  /-- Cocartesian structure on a dependent product; Definition 7.4.5 (Cat6). -/
  lf_opaque dependentProductCocartesian (A : SCat) (B : SCat) (E : SCat)
    (p : Functor E B) (u : Functor A B) (fib : Fibration E B p)
    (cocart : CocartesianFibrationWitness E B p fib) :
    CocartesianFibrationWitness (dependentProductTotal A B E p u) A
      (dependentProductProjection A B E p u) (dependentProductFibration A B E p u fib)

  /-- A fixed universe of categories, corresponding to the book's `Cat`; Definition 7.4.5. -/
  lf_opaque categoryUniverse : SCat
  /-- The fixed universe package; Definition 7.4.5. -/
  lf_opaque categoryUniverseWitness : UniverseWitness categoryUniverse
  /-- Terminal category is small in the universe of categories; Definition 7.4.5 (Cat2). -/
  lf_opaque terminalSmall : SmallWitness categoryUniverse terminalCat
  /-- Products of small categories are small; Definition 7.4.5 closure data. -/
  lf_opaque smallProduct (U : SCat) (C : SCat) (D : SCat)
    (hC : SmallWitness U C) (hD : SmallWitness U D) : SmallWitness U (prodCat C D)
  /-- Coproducts of small categories are small; Definition 7.4.5 closure data. -/
  lf_opaque smallCoproduct (U : SCat) (C : SCat) (D : SCat)
    (hC : SmallWitness U C) (hD : SmallWitness U D) : SmallWitness U (coprodCat C D)
  /-- Pullbacks of small categories are small; Definition 7.4.5 (Cat3). -/
  lf_opaque smallPullback (U : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (hC : SmallWitness U C) (hD : SmallWitness U D) (hE : SmallWitness U E) :
    SmallWitness U (pullbackCat C D E F G)
  /-- Functor categories of small categories are small; Definition 7.4.5 closure data. -/
  lf_opaque smallFunctorCategory (U : SCat) (C : SCat) (D : SCat)
    (hC : SmallWitness U C) (hD : SmallWitness U D) : SmallWitness U (funCat C D)
  /-- Subcategories of small categories are small; Definition 7.4.5 (Cat4). -/
  lf_opaque smallSubcategory (U : SCat) (C : SCat)
    (W : AnimaSubobject (morphismAnima C))
    (ids : containsIdentities C W) (comp : closedUnderComposition C W)
    (hC : SmallWitness U C) : SmallWitness U (subcategory C W ids comp)
  /-- Localizations of small categories are small; Definition 7.4.5 (Cat7). -/
  lf_opaque smallLocalization (U : SCat) (C : SCat)
    (W : AnimaSubobject (morphismAnima C))
    (hC : SmallWitness U C) : SmallWitness U (localizationCat C W)
  /-- Joins of small categories are small; Definition 7.4.5 (Cat5). -/
  lf_opaque smallJoin (U : SCat) (C : SCat) (D : SCat)
    (hC : SmallWitness U C) (hD : SmallWitness U D) : SmallWitness U (joinCat C D)
  /-- Dependent products of small cocartesian fibrations are small; Definition 7.4.5 (Cat6). -/
  lf_opaque smallDependentProductFibration (U : SCat)
    (A : SCat) (B : SCat) (E : SCat) (u : Functor A B) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (hA : SmallWitness U A)
    (hE : SmallCocartesianFibrationWitness U E B p fib cocart) :
    SmallCocartesianFibrationWitness U (dependentProductTotal A B E p u) A
      (dependentProductProjection A B E p u) (dependentProductFibration A B E p u fib)
      (dependentProductCocartesian A B E p u fib cocart)
  /-- Retracts of small categories are small; Definition 7.4.5 (Cat9). -/
  lf_opaque smallRetract (U : SCat) (C : SCat) (D : SCat)
    (i : Functor C D) (r : Functor D C)
    (ρ : NatIso C C (compFunctor C D C i r) (idFunctor C))
    (ret : RetractWitness C D i r ρ) (hD : SmallWitness U D) : SmallWitness U C
  /-- Cocartesian fibrations with small fibers are small; Definition 7.4.5 (Cat10). -/
  lf_opaque smallFibrationOfSmallFibers (U : SCat)
    (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (hFibers : SmallFibersWitness U E B p) :
    SmallCocartesianFibrationWitness U E B p fib cocart
  /-- Dependent products preserve small-fiber evidence; Definition 7.4.5 (Cat11). -/
  lf_opaque dependentProductSmallFibers (U : SCat)
    (A : SCat) (B : SCat) (E : SCat) (u : Functor A B) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (hE : SmallCocartesianFibrationWitness U E B p fib cocart)
    (hu : SmallFibersWitness U A B u) :
    SmallFibersWitness U (dependentProductTotal A B E p u) A
      (dependentProductProjection A B E p u)
  /-- A category is small when its interval mapping category is small; Definition 7.4.5 (Cat12). -/
  lf_opaque smallOfSmallIntervalMap (U : SCat) (C : SCat)
    (hMap : SmallWitness U (funCat intervalCat C)) : SmallWitness U C
  /-- Regularity of the universe of categories; Definition 7.4.5 (Cat1). -/
  lf_opaque categoryUniverseRegular :
    RegularUniverseWitness categoryUniverse categoryUniverseWitness
  /-- The terminal object of internal category theory in `Cat`, classified by the small terminal
  category.  Book context: Chapter 7 of the SCT book.
  -/
  lf_def catInternalTerminal : Obj categoryUniverse :=
    smallClassifyingMap categoryUniverse categoryUniverseWitness terminalCat terminalSmall
  /-- The universe classifier for terminal category agrees with the internal terminal object.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def catInternalTerminalSmall : SmallWitness categoryUniverse terminalCat := terminalSmall

namespace SCT

internal_defs where
  /-- The initial object of internal category theory in `Cat`.
  Book target: §7.5, derived from the small initial category.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def catInternalInitial : Obj categoryUniverse := sorry

  /-- Internal product operation in `Cat`.
  Book target: Lemma 7.5.5.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def catInternalProduct :
      Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse := sorry

  /-- Internal coproduct operation in `Cat`.
  Book target: Lemma 7.5.5.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def catInternalCoproduct :
      Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse := sorry

  /-- Internal pullback operation in `Cat`.
  Book target: §7.5.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def catInternalPullback :
      Functor (funCat pullbackShapeCat categoryUniverse) categoryUniverse := sorry

  /-- Internal functor-category/exponential operation in `Cat`.
  Book target: §7.5/Remark 7.5.15.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def catInternalFunctorCategory :
    Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse := sorry

end SCT
