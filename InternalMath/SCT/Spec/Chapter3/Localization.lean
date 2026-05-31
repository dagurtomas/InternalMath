/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter3.FullSubcategoryLifts

@[expose] public section

extend_type_theory SCT where

  model_section Chapter3

  /-- Universal lift through a full subcategory, derived from the subcategory universal property. -/
  lf_def fullSubcategoryLift : (D : SCat) ⇒ (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      (F : Functor D C) ⇒ LandsInObjectCollection D C P F ⇒ Functor D (fullSubcategory C P) :=
    fun D C P F h => subcategoryLift D C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P) F
      (landsInObjectCollectionPreservesFull D C P F h)
  /-- β comparison for the full-subcategory lift. -/
  lf_def fullSubcategoryLiftBeta : (D : SCat) ⇒ (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      (F : Functor D C) ⇒ (h : LandsInObjectCollection D C P F) ⇒
        NatIso D C
          (compFunctor D (fullSubcategory C P) C (fullSubcategoryLift D C P F h)
            (fullSubcategoryIncl C P))
          F :=
    fun D C P F h => subcategoryLiftBeta D C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P) F
      (landsInObjectCollectionPreservesFull D C P F h)
  /-- Uniqueness of lifts through full subcategories. -/
  lf_def fullSubcategoryLiftUniq : (D : SCat) ⇒ (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      (F : Functor D C) ⇒ (h : LandsInObjectCollection D C P F) ⇒
      (K : Functor D (fullSubcategory C P)) ⇒
      (β : NatIso D C (compFunctor D (fullSubcategory C P) C K
        (fullSubcategoryIncl C P)) F) ⇒
        NatIso D (fullSubcategory C P) K (fullSubcategoryLift D C P F h) :=
    fun D C P F h K β => subcategoryLiftUniq D C (fullSubcategoryMorphismCollection C P)
      (fullSubcategoryMorphismContainsIdentities C P) (fullSubcategoryMorphismClosed C P) F
      (landsInObjectCollectionPreservesFull D C P F h) K β

  /-- Evidence that a functor sends a morphism collection to isomorphisms; Axiom I. -/
  syntax_sort InvertsMorphismCollection (C : SCat) (D : SCat)
    (W : MorphismCollection C) (F : Functor C D) : Type u
  syntax_sort_role InvertsMorphismCollection : side_structure
  /-- Localization at a morphism collection; Axiom I. -/
  lf_opaque localizationCat (C : SCat) (W : MorphismCollection C) : SCat

extend_type_theory SCT where

  model_section Chapter3

  /-- Membership of a functor object in the object collection of functors inverting `W`. -/
  syntax_abbrev InvertingFunctorObjectMember (C : SCat) (D : SCat)
    (W : MorphismCollection C) (P : ObjectCollection (funCat C D)) (F : Functor C D) :=
    ObjectCollectionMember (funCat C D) P (functorObject C D F)
  /-- Comprehension package for the full subcategory of functors inverting `W`.
  Book target: Definition 3.3.2. -/
  lf_opaque invertingFunctorObjectPackage (C : SCat) (D : SCat) (W : MorphismCollection C) :
    Σ P : ObjectCollection (funCat C D),
      (F : Functor C D) →
        Σ intro : InvertsMorphismCollection C D W F → InvertingFunctorObjectMember C D W P F,
          InvertingFunctorObjectMember C D W P F → InvertsMorphismCollection C D W F
  /-- Object collection of functors that invert a morphism collection. -/
  lf_def invertingFunctorObjects : (C : SCat) ⇒ (D : SCat) ⇒ MorphismCollection C ⇒
      ObjectCollection (funCat C D) :=
    fun C D W => fst (invertingFunctorObjectPackage C D W)
  /-- Inverting evidence gives membership in the inverting-functor object collection. -/
  lf_def invertingFunctorObjectIntro : (C : SCat) ⇒ (D : SCat) ⇒
      (W : MorphismCollection C) ⇒ (F : Functor C D) ⇒ InvertsMorphismCollection C D W F →
        InvertingFunctorObjectMember C D W (invertingFunctorObjects C D W) F :=
    fun C D W F h => fst (snd (invertingFunctorObjectPackage C D W) F) h
  /-- Membership in the inverting-functor object collection gives inverting evidence. -/
  lf_def invertingFunctorObjectElim : (C : SCat) ⇒ (D : SCat) ⇒
      (W : MorphismCollection C) ⇒ (F : Functor C D) ⇒
        InvertingFunctorObjectMember C D W (invertingFunctorObjects C D W) F →
          InvertsMorphismCollection C D W F :=
    fun C D W F h => snd (snd (invertingFunctorObjectPackage C D W) F) h

  /-- Full subcategory of functors that invert a morphism collection; Definition 3.3.2. -/
  lf_def invertingFunctorCat : (C : SCat) ⇒ (D : SCat) ⇒ MorphismCollection C ⇒ SCat :=
    fun C D W => fullSubcategory (funCat C D) (invertingFunctorObjects C D W)
  /-- Inclusion of inverting functors into the ordinary functor category; Definition 3.3.2. -/
  lf_def invertingFunctorIncl : (C : SCat) ⇒ (D : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (invertingFunctorCat C D W) (funCat C D) :=
    fun C D W => fullSubcategoryIncl (funCat C D) (invertingFunctorObjects C D W)
  /-- The inverting-functor inclusion is a full subcategory, by construction. -/
  lf_def invertingFunctorSubcategoryWitness :
      (C : SCat) ⇒ (D : SCat) ⇒ (W : MorphismCollection C) ⇒
        SubcategoryWitness (invertingFunctorCat C D W) (funCat C D)
          (invertingFunctorIncl C D W) :=
    fun C D W => fullSubcategoryInclWitness (funCat C D) (invertingFunctorObjects C D W)

namespace SCT

/- Theorem-shaped declaration admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- If the target is a groupoid, every functor inverts the selected morphisms.
  Book target: Definition 3.3.2, functors that invert a chosen collection of morphisms.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove that all morphisms in a groupoid are invertible, then show the
  inverting-functor object collection is all of `Fun(C,D)`.
  -/
  def invertingFunctorTargetGroupoidEquiv (C : SCat) (D : SCat)
    (W : MorphismCollection C) (gD : GroupoidWitness D) :
    CatEquiv (invertingFunctorCat C D W) (funCat C D) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Localization functor; Axiom I. -/
  lf_opaque localizationFunctor (C : SCat) (W : MorphismCollection C) :
    Functor C (localizationCat C W)
  /-- The localization functor inverts the chosen morphisms; Axiom I. -/
  lf_opaque localizationInverts (C : SCat) (W : MorphismCollection C) :
    InvertsMorphismCollection C (localizationCat C W) W (localizationFunctor C W)
  /-- Localization universal package.  It stores the mapping-category equivalence,
  descents of inverting functors, their β comparisons, and uniqueness of descents. -/
  lf_opaque localizationUniversalPackage (C : SCat) (W : MorphismCollection C) (D : SCat) :
    Σ e : CatEquiv (funCat (localizationCat C W) D) (invertingFunctorCat C D W),
      (F : Functor C D) → (h : InvertsMorphismCollection C D W F) →
        Σ K : Functor (localizationCat C W) D,
          Σ β : NatIso C D (compFunctor C (localizationCat C W) D
            (localizationFunctor C W) K) F,
            (L : Functor (localizationCat C W) D) →
              NatIso C D (compFunctor C (localizationCat C W) D
                (localizationFunctor C W) L) F → NatIso (localizationCat C W) D L K
  /-- Descend a functor that inverts the localized morphisms; Axiom I. -/
  lf_def localizationDesc : (C : SCat) ⇒ (W : MorphismCollection C) ⇒ (D : SCat) ⇒
      (F : Functor C D) ⇒ InvertsMorphismCollection C D W F ⇒
      Functor (localizationCat C W) D :=
    fun C W D F h => fst (snd (localizationUniversalPackage C W D) F h)
  /-- β comparison for localization descent; Axiom I. -/
  lf_def localizationDescBeta : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (D : SCat) ⇒ (F : Functor C D) ⇒ (h : InvertsMorphismCollection C D W F) ⇒
      NatIso C D
        (compFunctor C (localizationCat C W) D
          (localizationFunctor C W) (localizationDesc C W D F h)) F :=
    fun C W D F h => fst (snd (snd (localizationUniversalPackage C W D) F h))
  /-- Uniqueness of localization descents; Axiom I. -/
  lf_def localizationDescUniq : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (D : SCat) ⇒ (F : Functor C D) ⇒ (h : InvertsMorphismCollection C D W F) ⇒
      (K : Functor (localizationCat C W) D) ⇒
      NatIso C D (compFunctor C (localizationCat C W) D
        (localizationFunctor C W) K) F ⇒
      NatIso (localizationCat C W) D K (localizationDesc C W D F h) :=
    fun C W D F h K β => snd (snd (snd (localizationUniversalPackage C W D) F h)) K β
  /-- Universal equivalence `Fun(C[W^{-1}],D) ≃ Fun^W(C,D)` for localizations.  Book context:
  Chapter 3 of the SCT book.
  -/
  lf_def localizationUniversalEquiv : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      (D : SCat) ⇒ CatEquiv (funCat (localizationCat C W) D) (invertingFunctorCat C D W) :=
    fun C W D => fst (localizationUniversalPackage C W D)
  /-- Selected morphisms as interval-shaped arrows in `C`.  Book context: Chapter 3 of the SCT book.
  -/
  lf_def morphismCollectionArrowObject : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (morphismCollectionCat C W) (funCat intervalCat C) :=
    fun C W => compFunctor (morphismCollectionCat C W) (coreCat (funCat intervalCat C))
      (funCat intervalCat C) (morphismCollectionIncl C W) (coreIncl (funCat intervalCat C))
  /-- Source of a selected morphism.  Book context: Chapter 3 of the SCT book. -/
  lf_def morphismCollectionSourceFunctor : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (morphismCollectionCat C W) C :=
    fun C W => compFunctor (morphismCollectionCat C W) (funCat intervalCat C) C
      (morphismCollectionArrowObject C W) (sourceFunctor C)
  /-- The arrow map `[1] × W → C` adjoint to the selected morphisms.  Book context: Chapter 3 of the
  SCT book.
  -/
  lf_def morphismCollectionArrowFunctor : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (prodCat intervalCat (morphismCollectionCat C W)) C :=
    fun C W => compFunctor (prodCat intervalCat (morphismCollectionCat C W))
      (prodCat (funCat intervalCat C) intervalCat) C
      (prodPair (prodCat intervalCat (morphismCollectionCat C W))
        (funCat intervalCat C) intervalCat
        (compFunctor (prodCat intervalCat (morphismCollectionCat C W))
          (morphismCollectionCat C W) (funCat intervalCat C)
          (prodPr2 intervalCat (morphismCollectionCat C W))
          (morphismCollectionArrowObject C W))
        (prodPr1 intervalCat (morphismCollectionCat C W)))
      (evalFunctor intervalCat C)
  /-- The bottom map `W → C[W^{-1}]` in the localization pushout square, chosen via sources.  Book
  context: Chapter 3 of the SCT book.
  -/
  lf_def localizationCollectionFunctor : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (morphismCollectionCat C W) (localizationCat C W) :=
    fun C W => compFunctor (morphismCollectionCat C W) C (localizationCat C W)
      (morphismCollectionSourceFunctor C W) (localizationFunctor C W)

  /-- Geometric realization is localization at all morphisms; Axiom J. -/
  lf_def geometricRealization : SCat ⇒ SCat := fun C => localizationCat C (allMorphisms C)

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Pushout-square presentation of localization; Remark 3.3.8.
  Status: temporary sorry-admitted structural theorem package; not a model field. -/
  def localizationPushoutSquare (C : SCat) (W : MorphismCollection C) :
    PushoutSquare (prodCat intervalCat (morphismCollectionCat C W)) C
      (morphismCollectionCat C W) (localizationCat C W)
      (morphismCollectionArrowFunctor C W) (prodPr2 intervalCat (morphismCollectionCat C W))
      (localizationFunctor C W) (localizationCollectionFunctor C W) :=
    sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Commutativity component of the localization pushout square. -/
  lf_def localizationPushoutSquareComm : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      NatIso (prodCat intervalCat (morphismCollectionCat C W)) (localizationCat C W)
        (compFunctor (prodCat intervalCat (morphismCollectionCat C W)) C (localizationCat C W)
          (morphismCollectionArrowFunctor C W) (localizationFunctor C W))
        (compFunctor (prodCat intervalCat (morphismCollectionCat C W))
          (morphismCollectionCat C W) (localizationCat C W)
          (prodPr2 intervalCat (morphismCollectionCat C W))
          (localizationCollectionFunctor C W)) :=
    fun C W => pushoutSquareComm (prodCat intervalCat (morphismCollectionCat C W)) C
      (morphismCollectionCat C W) (localizationCat C W) (morphismCollectionArrowFunctor C W)
      (prodPr2 intervalCat (morphismCollectionCat C W)) (localizationFunctor C W)
      (localizationCollectionFunctor C W) (localizationPushoutSquare C W)

extend_type_theory SCT where

  model_section Chapter3

  /-- The realization functor; Axiom I and Axiom J. -/
  lf_def geometricRealizationFunctor : (C : SCat) ⇒ Functor C (geometricRealization C) :=
    fun C => localizationFunctor C (allMorphisms C)
  /-- Realization is universal for maps from `C` to groupoids.  Book context: Chapter 3 of the SCT
  book.
  -/
  lf_def geometricRealizationUniversalGroupoid : (C : SCat) ⇒ (G : SCat) ⇒
      GroupoidWitness G ⇒ CatEquiv (funCat (geometricRealization C) G) (funCat C G) :=
    fun C G gG => catEquivTrans (funCat (geometricRealization C) G)
      (invertingFunctorCat C G (allMorphisms C)) (funCat C G)
      (localizationUniversalEquiv C (allMorphisms C) G)
      (invertingFunctorTargetGroupoidEquiv C G (allMorphisms C) gG)
  /-- A functor over a fixed base, represented by a natural isomorphism over the base.  Book
  context: Chapter 3 of the SCT book.
  -/
  syntax_abbrev FunctorOver (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (q : Functor F B) (u : Functor E F) :=
    NatIso E B (compFunctor E F B u q) p

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Geometric realizations are anima.
  Book target: Proposition 3.4.5 and the groupoid/anima identification of Axiom G.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove that localization at all morphisms is groupoidal and transport
  it to an anima via `groupoid_is_anima_cat`.
  -/
  def geometric_realization_is_anima (C : SCat) : isAnimaCat (geometricRealization C) := sorry

  /-- Categories over a base, used for exponentiable functors.
  Book target: Definition 3.5.4, the over-category `Cat/C` of categories over a base.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct as the appropriate slice/fiber of a functor category. -/
  def overCat (B : SCat) : SCat := sorry

end SCT
