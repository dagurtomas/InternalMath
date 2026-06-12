/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter1.BasicConstructions

/-!
# Chapter 1 cells, squares, Segal composition, and invertible arrows

This file connects natural transformations with arrows in functor categories and then records the
square and Segal axioms used for composition.

Book guide, paraphrasing the May 2026 draft:

- Natural transformations `F ⟶ G` are arrows in `Fun(C,D)`. The file makes this explicit with
  `natTransCat`, `natTransObject`, `natTransUnderlyingArrow`, and `natTransComponent`.
- Axiom D says that restricting a square `[1] × [1] ⟶ C` to two compatible triangles gives an
  equivalence. The split data is `squareRestriction`, `squareExtension`,
  `squareRestrictionUnit`, and `squareRestrictionCounit`; `squareRestrictionEquiv` packages it.
- Axiom E says restriction from `[2]`-diagrams to composable pairs is an equivalence. The split data
  is `segalRestriction`, `segalExtension`, `segalUnit`, and `segalCounit`; `segalEquiv` packages it.
- Composition of interval-shaped arrows is extracted from Axiom E via `composablePair`,
  `compositeOfComposablePair`, and `composeComposableMorphism`. The unit and associativity fields
  are the split coherence data for this chosen composition.
- Invertible interval-shaped morphisms are represented by the checked package
  `InvertibleMorphismData`: an inverse arrow, endpoint comparisons, and left/right unit
  comparisons.

The Rezk category `Iso(C)` and the Rezk equivalence are built in `Chapter1/IsoRezk.lean` from this
invertible-arrow package and the Chapter 3 full-subcategory API.
-/

@[expose] public section

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Decode an object of a functor category back to its represented functor.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_def functorFromObject : (C : SCat) ⇒ (D : SCat) ⇒ Obj (funCat C D) ⇒ Functor C D :=
    fun C D X => compFunctor C (prodCat terminalCat C) D
      (prodPair C terminalCat C (terminalProjection C) (idFunctor C))
      (uncurryFunctor terminalCat C D X)
  /-- Source fiber of the arrow category of `Fun(C,D)` over a functor object.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_def natTransSourceFiberCat : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒ SCat :=
    fun C D F => pullbackCat (funCat intervalCat (funCat C D)) terminalCat (funCat C D)
      (sourceFunctor (funCat C D)) (functorObject C D F)
  /-- Target map from the source fiber of natural transformations.  Book context: Chapter 1 of the
  SCT book.
  -/
  lf_def natTransSourceFiberTarget : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      Functor (natTransSourceFiberCat C D F) (funCat C D) :=
    fun C D F => compFunctor (natTransSourceFiberCat C D F)
      (funCat intervalCat (funCat C D)) (funCat C D)
      (pullbackPr1 (funCat intervalCat (funCat C D)) terminalCat (funCat C D)
        (sourceFunctor (funCat C D)) (functorObject C D F))
      (targetFunctor (funCat C D))
  /-- Category of natural transformations from `F` to `G`, as a fiber of `Fun([1],Fun(C,D))`.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_def natTransCat : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒ Functor C D ⇒ SCat :=
    fun C D F G => pullbackCat (natTransSourceFiberCat C D F) terminalCat (funCat C D)
      (natTransSourceFiberTarget C D F) (functorObject C D G)
  /-- A natural transformation, viewed as an object of the explicit natural-transformation
  category.  This records the Chapter 1 identification of natural transformations with arrows in
  `Fun(C,D)` while `NatTrans` is primitive vocabulary. -/
  lf_opaque natTransObject (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D)
    (α : NatTrans F G) : Obj (natTransCat C D F G)

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Regard a natural isomorphism as its underlying natural transformation. -/
  lf_def natIsoToNatTrans : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ NatIso F G ⇒ NatTrans F G :=
    fun C D F G α => π₁ α

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Higher isomorphisms between natural isomorphisms, represented in the natural-transformation
  fiber.  Book context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev NatIsoIso {C : SCat} {D : SCat} {F : Functor C D} {G : Functor C D}
    (α : NatIso F G) (β : NatIso F G) := ObjIso (natTransCat C D F G)
      (natTransObject C D F G (natIsoToNatTrans C D F G α))
      (natTransObject C D F G (natIsoToNatTrans C D F G β))
  /-- Underlying arrow in the functor category represented by a natural transformation.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_def natTransUnderlyingArrow : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ NatTrans F G ⇒ Functor intervalCat (funCat C D) :=
    fun C D F G α => functorFromObject intervalCat (funCat C D)
      (compFunctor terminalCat (natTransCat C D F G) (funCat intervalCat (funCat C D))
        (natTransObject C D F G α)
        (compFunctor (natTransCat C D F G) (natTransSourceFiberCat C D F)
          (funCat intervalCat (funCat C D))
          (pullbackPr1 (natTransSourceFiberCat C D F) terminalCat (funCat C D)
            (natTransSourceFiberTarget C D F) (functorObject C D G))
          (pullbackPr1 (funCat intervalCat (funCat C D)) terminalCat (funCat C D)
            (sourceFunctor (funCat C D)) (functorObject C D F))))
  /-- Component of a natural transformation at an absolute object.  Book context: Chapter 1 of the
  SCT book.
  -/
  lf_def natTransComponent : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ NatTrans F G ⇒ Obj C ⇒ Functor intervalCat D :=
    fun C D F G α x => compFunctor intervalCat (prodCat intervalCat C) D
      (prodPair intervalCat intervalCat C (idFunctor intervalCat) (constantFunctor intervalCat C x))
      (uncurryFunctor intervalCat C D (natTransUnderlyingArrow C D F G α))
  /-- Reflexivity higher isomorphism between natural isomorphisms.  Book context: Chapter 1 of the
  SCT book.
  -/
  lf_def idNatIsoIso : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ (α : NatIso F G) ⇒ NatIsoIso α α :=
    fun C D F G α => idNatIso terminalCat (natTransCat C D F G)
      (natTransObject C D F G (natIsoToNatTrans C D F G α))
  /-- Compatibility data for a morphism between pullback cones.  This admitted definition records
  the `NatIsoIso` coherence between the two paths around the cospan target without introducing new
  primitive vocabulary. -/
  syntax_def PullbackConeIsoCompat (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) (A₀ : Functor X C) (A₁ : Functor X C)
    (B₀ : Functor X D) (B₁ : Functor X D)
    (θ₀ : NatIso X E (compFunctor X C E A₀ F) (compFunctor X D E B₀ G))
    (θ₁ : NatIso X E (compFunctor X C E A₁ F) (compFunctor X D E B₁ G))
    (α : NatIso X C A₀ A₁) (β : NatIso X D B₀ B₁) : Type u := sorry
  syntax_sort_role PullbackConeIsoCompat : side_structure
  /-- Isomorphism between two pullback cones, including projection isomorphisms and cospan
  compatibility.  This is admitted package debt, not primitive vocabulary. -/
  syntax_def PullbackConeIso (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (u : PullbackCone X C D E F G) (v : PullbackCone X C D E F G) : Type u := sorry
  syntax_sort_role PullbackConeIso : side_structure

namespace SCT

/- Cone-isomorphism projections are admitted temporarily while the compatibility package is refined
   to the concrete `NatIsoIso` coherence. -/
internal_defs where
  /-- Left projection of a cone isomorphism. -/
  def pullbackConeIsoLeft (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (u : PullbackCone X C D E F G) (v : PullbackCone X C D E F G)
      (η : PullbackConeIso X C D E F G u v) :
      NatIso X C (pullbackConeLeft X C D E F G u)
        (pullbackConeLeft X C D E F G v) := sorry
  /-- Right projection of a cone isomorphism. -/
  def pullbackConeIsoRight (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (u : PullbackCone X C D E F G) (v : PullbackCone X C D E F G)
      (η : PullbackConeIso X C D E F G u v) :
      NatIso X D (pullbackConeRight X C D E F G u)
        (pullbackConeRight X C D E F G v) := sorry
  /-- Compatibility projection of a cone isomorphism. -/
  def pullbackConeIsoCompatibility (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (u : PullbackCone X C D E F G) (v : PullbackCone X C D E F G)
      (η : PullbackConeIso X C D E F G u v) :
      PullbackConeIsoCompat X C D E F G
        (pullbackConeLeft X C D E F G u) (pullbackConeLeft X C D E F G v)
        (pullbackConeRight X C D E F G u) (pullbackConeRight X C D E F G v)
        (pullbackConeComm X C D E F G u) (pullbackConeComm X C D E F G v)
        (pullbackConeIsoLeft X C D E F G u v η)
        (pullbackConeIsoRight X C D E F G u v η) := sorry
  /-- Natural isomorphisms into the pullback project to compatible cone isomorphisms. -/
  def pullbackConeIsoOfNatIso (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (H : Functor X (pullbackCat C D E F G))
      (K : Functor X (pullbackCat C D E F G))
      (γ : NatIso X (pullbackCat C D E F G) H K) :
      PullbackConeIso X C D E F G (pullbackConeOfMap X C D E F G H)
        (pullbackConeOfMap X C D E F G K) := sorry
  /-- Packaged β isomorphism from the lifted cone to the input cone. -/
  def pullbackLiftConeBeta (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E) (u : PullbackCone X C D E F G) :
      PullbackConeIso X C D E F G
        (pullbackConeOfMap X C D E F G (pullbackLiftCone X C D E F G u)) u := sorry

end SCT

namespace SCT

/- Pullback-cone uniqueness and finite bicategorical coherence are theorem-shaped definition
   debt. -/
internal_defs where
  /-- Uniqueness for maps into a pullback from compatible cone isomorphism data; Axiom B.5. -/
  def pullbackUniqCone (X : SCat) (C : SCat) (D : SCat) (E : SCat)
      (F : Functor C E) (G : Functor D E)
      (H : Functor X (pullbackCat C D E F G)) (K : Functor X (pullbackCat C D E F G))
      (η : PullbackConeIso X C D E F G (pullbackConeOfMap X C D E F G H)
        (pullbackConeOfMap X C D E F G K)) : NatIso X (pullbackCat C D E F G) H K :=
    sorry
  /-- Horizontal composition preserves identity natural isomorphisms. -/
  def horizCompIdId (B : SCat) (C : SCat) (D : SCat)
      (F : Functor B C) (G : Functor C D) :
      NatIsoIso B D (compFunctor B C D F G) (compFunctor B C D F G)
        (horizCompNatIso B C D F F G G (idNatIso B C F) (idNatIso C D G))
        (idNatIso B D (compFunctor B C D F G)) :=
    sorry
  /-- Horizontal composition preserves vertical composition. -/
  def horizCompCompComp (B : SCat) (C : SCat) (D : SCat)
      (F₀ : Functor B C) (F₁ : Functor B C) (F₂ : Functor B C)
      (G₀ : Functor C D) (G₁ : Functor C D) (G₂ : Functor C D)
      (α₀ : NatIso B C F₀ F₁) (α₁ : NatIso B C F₁ F₂)
      (β₀ : NatIso C D G₀ G₁) (β₁ : NatIso C D G₁ G₂) :
      NatIsoIso B D (compFunctor B C D F₀ G₀) (compFunctor B C D F₂ G₂)
        (horizCompNatIso B C D F₀ F₂ G₀ G₂
          (compNatIso B C F₀ F₁ F₂ α₀ α₁) (compNatIso C D G₀ G₁ G₂ β₀ β₁))
        (compNatIso B D (compFunctor B C D F₀ G₀) (compFunctor B C D F₁ G₁)
          (compFunctor B C D F₂ G₂)
          (horizCompNatIso B C D F₀ F₁ G₀ G₁ α₀ β₀)
          (horizCompNatIso B C D F₁ F₂ G₁ G₂ α₁ β₁)) :=
    sorry
  /-- Horizontal composition by an identity on the left is compatible with unitors. -/
  def horizCompLeftId (B : SCat) (C : SCat) (D : SCat)
      (F : Functor B C) (G : Functor B C) (H : Functor C D)
      (α : NatIso B C F G) :
      NatIsoIso B D (compFunctor B C D F H) (compFunctor B C D G H)
        (horizCompNatIso B C D F G H H α (idNatIso C D H))
        (postWhiskerNatIso B C D F G H α) :=
    sorry
  /-- Horizontal composition by an identity on the right is compatible with unitors. -/
  def horizCompRightId (B : SCat) (C : SCat) (D : SCat)
      (F : Functor B C) (G : Functor C D) (H : Functor C D)
      (α : NatIso C D G H) :
      NatIsoIso B D (compFunctor B C D F G) (compFunctor B C D F H)
        (horizCompNatIso B C D F F G H (idNatIso B C F) α)
        (preWhiskerNatIso B C D F G H α) :=
    sorry
  /-- Associator naturality for whiskered natural isomorphisms. -/
  def assocFunctorNaturality (A : SCat) (B : SCat) (C : SCat) (D : SCat)
      (F₀ : Functor A B) (F₁ : Functor A B)
      (G₀ : Functor B C) (G₁ : Functor B C)
      (H₀ : Functor C D) (H₁ : Functor C D)
      (α : NatIso A B F₀ F₁) (β : NatIso B C G₀ G₁) (γ : NatIso C D H₀ H₁) :
      NatIsoIso A D
        (compFunctor A C D (compFunctor A B C F₀ G₀) H₀)
        (compFunctor A B D F₁ (compFunctor B C D G₁ H₁))
        (compNatIso A D
          (compFunctor A C D (compFunctor A B C F₀ G₀) H₀)
          (compFunctor A C D (compFunctor A B C F₁ G₁) H₁)
          (compFunctor A B D F₁ (compFunctor B C D G₁ H₁))
          (horizCompNatIso A C D (compFunctor A B C F₀ G₀)
            (compFunctor A B C F₁ G₁) H₀ H₁
            (horizCompNatIso A B C F₀ F₁ G₀ G₁ α β) γ)
          (assocFunctor A B C D F₁ G₁ H₁))
        (compNatIso A D
          (compFunctor A C D (compFunctor A B C F₀ G₀) H₀)
          (compFunctor A B D F₀ (compFunctor B C D G₀ H₀))
          (compFunctor A B D F₁ (compFunctor B C D G₁ H₁))
          (assocFunctor A B C D F₀ G₀ H₀)
          (horizCompNatIso A B D F₀ F₁ (compFunctor B C D G₀ H₀)
            (compFunctor B C D G₁ H₁) α
            (horizCompNatIso B C D G₀ G₁ H₀ H₁ β γ))) :=
    sorry

end SCT

extend_type_theory SCT where

  model_section Chapter1

  /-- Identity interval-shaped morphism at an object; Axioms A.3 and C.1. -/
  lf_def identityMorphism : (C : SCat) ⇒ (x : Obj C) ⇒ Functor intervalCat C :=
    fun C x => compFunctor intervalCat terminalCat C (terminalProjection intervalCat) x
  /-- Endpoint compatibility for a constant interval-shaped morphism.
  Book context:Chapter 1 of the
  SCT book.
  -/
  lf_def identityMorphismEndpointCompat : (C : SCat) ⇒ (e : Obj intervalCat) ⇒ (x : Obj C) ⇒
      NatIso terminalCat C (compFunctor terminalCat intervalCat C e (identityMorphism C x)) x :=
    fun C e x => compNatIso terminalCat C
      (compFunctor terminalCat intervalCat C e (identityMorphism C x))
      (compFunctor terminalCat terminalCat C
        (compFunctor terminalCat intervalCat terminalCat e (terminalProjection intervalCat)) x)
      x
      (assocFunctorInv terminalCat intervalCat terminalCat C e (terminalProjection intervalCat) x)
      (compNatIso terminalCat C
        (compFunctor terminalCat terminalCat C
          (compFunctor terminalCat intervalCat terminalCat e (terminalProjection intervalCat)) x)
        (compFunctor terminalCat terminalCat C (idFunctor terminalCat) x)
        x
        (postWhiskerNatIso terminalCat terminalCat C
          (compFunctor terminalCat intervalCat terminalCat e (terminalProjection intervalCat))
          (idFunctor terminalCat) x
          (terminalUnique terminalCat
            (compFunctor terminalCat intervalCat terminalCat e (terminalProjection intervalCat))
            (idFunctor terminalCat)))
        (leftUnitor terminalCat C x))
  /-- Source law for identity interval-shaped morphisms; Axiom C.1. -/
  lf_def identityMorphismSourceCompat : (C : SCat) ⇒ (x : Obj C) ⇒
      NatIso terminalCat C (sourceObj C (identityMorphism C x)) x :=
    fun C x => identityMorphismEndpointCompat C intervalZero x
  /-- Target law for identity interval-shaped morphisms; Axiom C.1. -/
  lf_def identityMorphismTargetCompat : (C : SCat) ⇒ (x : Obj C) ⇒
      NatIso terminalCat C (targetObj C (identityMorphism C x)) x :=
    fun C x => identityMorphismEndpointCompat C intervalOne x
  /-- Category of composable pairs, defined as a pullback; Axiom E. -/
  lf_def composableMorphismsCat : SCat ⇒ SCat :=
    fun C => pullbackCat (funCat intervalCat C) (funCat intervalCat C) C
      (targetFunctor C) (sourceFunctor C)

  /-- Boundary category of compatible square restrictions; Axiom D. -/
  lf_def compatibleTriangleCat : SCat ⇒ SCat :=
    fun C => pullbackCat (funCat simplex2Cat C) (funCat simplex2Cat C)
      (funCat intervalCat C)
      (precompFunctor intervalCat simplex2Cat C simplex2FaceD1)
      (precompFunctor intervalCat simplex2Cat C simplex2FaceD1)

namespace SCT

/- The named square and Segal restriction functors are definition-shaped debt.  Axiom D and Axiom E
   are recorded below as split inverse/unit/counit data pinned to these functors. -/
internal_defs where
  /-- Lower triangular inclusion `[2] → [1] × [1]`; Axiom D. -/
  def squareLowerTriangle : Functor simplex2Cat squareCat := sorry
  /-- Upper triangular inclusion `[2] → [1] × [1]`; Axiom D. -/
  def squareUpperTriangle : Functor simplex2Cat squareCat := sorry
  /-- Restriction of a square to compatible triangle data; Axiom D. -/
  def squareRestriction (C : SCat) :
    Functor (funCat squareCat C) (compatibleTriangleCat C) := sorry
  /-- Segal restriction from `[2]`-diagrams to composable-pair data; Axiom E. -/
  def segalRestriction (C : SCat) :
    Functor (funCat simplex2Cat C) (composableMorphismsCat C) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter1

  /-- Chosen extension of compatible triangle data to a square; Axiom D for the named
  restriction. -/
  lf_opaque squareExtension (C : SCat) :
    Functor (compatibleTriangleCat C) (funCat squareCat C)
  /-- Unit for the square-restriction equivalence; Axiom D for the named restriction. -/
  lf_opaque squareRestrictionUnit (C : SCat) :
    NatIso (funCat squareCat C) (funCat squareCat C)
      (compFunctor (funCat squareCat C) (compatibleTriangleCat C) (funCat squareCat C)
        (squareRestriction C) (squareExtension C))
      (idFunctor (funCat squareCat C))
  /-- Counit for the square-restriction equivalence; Axiom D for the named restriction. -/
  lf_opaque squareRestrictionCounit (C : SCat) :
    NatIso (compatibleTriangleCat C) (compatibleTriangleCat C)
      (compFunctor (compatibleTriangleCat C) (funCat squareCat C)
        (compatibleTriangleCat C) (squareExtension C) (squareRestriction C))
      (idFunctor (compatibleTriangleCat C))
  /-- Packaged square-restriction equivalence; Axiom D. -/
  lf_def squareRestrictionEquiv :
      (C : SCat) ⇒ CatEquiv (funCat squareCat C) (compatibleTriangleCat C) :=
    fun C => catEquivOfData (funCat squareCat C) (compatibleTriangleCat C)
      (squareRestriction C) (squareExtension C)
      (squareRestrictionUnit C) (squareRestrictionCounit C)

  /-- Chosen inverse/extension for the Segal restriction; Axiom E for the named restriction. -/
  lf_opaque segalExtension (C : SCat) :
    Functor (composableMorphismsCat C) (funCat simplex2Cat C)
  /-- Unit for the Segal equivalence; Axiom E for the named restriction. -/
  lf_opaque segalUnit (C : SCat) :
    NatIso (funCat simplex2Cat C) (funCat simplex2Cat C)
      (compFunctor (funCat simplex2Cat C) (composableMorphismsCat C)
        (funCat simplex2Cat C) (segalRestriction C) (segalExtension C))
      (idFunctor (funCat simplex2Cat C))
  /-- Counit for the Segal equivalence; Axiom E for the named restriction. -/
  lf_opaque segalCounit (C : SCat) :
    NatIso (composableMorphismsCat C) (composableMorphismsCat C)
      (compFunctor (composableMorphismsCat C) (funCat simplex2Cat C)
        (composableMorphismsCat C) (segalExtension C) (segalRestriction C))
      (idFunctor (composableMorphismsCat C))
  /-- Packaged Segal equivalence; Axiom E. -/
  lf_def segalEquiv :
      (C : SCat) ⇒ CatEquiv (funCat simplex2Cat C) (composableMorphismsCat C) :=
    fun C => catEquivOfData (funCat simplex2Cat C) (composableMorphismsCat C)
      (segalRestriction C) (segalExtension C) (segalUnit C) (segalCounit C)

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- A composable pair built from arrows and endpoint compatibility, using the defining pullback
  for composable arrows; Axiom E. -/
  lf_def composablePair : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      (g : Functor intervalCat C) ⇒
      NatIso terminalCat C (targetObj C f) (sourceObj C g) ⇒
      Obj (composableMorphismsCat C) :=
    fun C f g α =>
      pullbackLift terminalCat (funCat intervalCat C) (funCat intervalCat C) C
        (targetFunctor C) (sourceFunctor C)
        (functorObject intervalCat C f) (functorObject intervalCat C g)
        (compNatIso terminalCat C
          (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C f)
            (targetFunctor C))
          (targetObj C f)
          (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C g)
            (sourceFunctor C))
          (functorObjectTargetCompat C f)
          (compNatIso terminalCat C
            (targetObj C f) (sourceObj C g)
            (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C g)
              (sourceFunctor C))
            α
            (invNatIso terminalCat C
              (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C g)
                (sourceFunctor C))
              (sourceObj C g)
              (functorObjectSourceCompat C g))))
  /-- Composite arrow extracted from a composable pair by extending along the Segal equivalence and
  restricting to the long edge; Axiom E. -/
  lf_def compositeOfComposablePair : (C : SCat) ⇒
      Obj (composableMorphismsCat C) ⇒ Functor intervalCat C :=
    fun C p => compFunctor intervalCat simplex2Cat C simplex2FaceD1
      (functorFromObject simplex2Cat C
        (compFunctor terminalCat (composableMorphismsCat C) (funCat simplex2Cat C) p
          (segalExtension C)))

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Binary composition of endpoint-compatible morphisms, extracted by Segal; Axiom E. -/
  lf_def composeComposableMorphism : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      (g : Functor intervalCat C) ⇒
      NatIso terminalCat C (targetObj C f) (sourceObj C g) ⇒ Functor intervalCat C :=
    fun C f g α => compositeOfComposablePair C (composablePair C f g α)

namespace SCT

/- Endpoint laws for the chosen Segal composite are visible coherence debt. -/
internal_defs where
  /-- Source law for a Segal composite; consequence of Axiom E. -/
  def compositeSourceCompat (C : SCat) (p : Obj (composableMorphismsCat C)) :
      NatIso terminalCat C (sourceObj C (compositeOfComposablePair C p))
        (compFunctor terminalCat (funCat intervalCat C) C
          (compFunctor terminalCat (composableMorphismsCat C) (funCat intervalCat C) p
            (pullbackPr1 (funCat intervalCat C) (funCat intervalCat C) C
              (targetFunctor C) (sourceFunctor C)))
          (sourceFunctor C)) :=
    sorry
  /-- Target law for a Segal composite; consequence of Axiom E. -/
  def compositeTargetCompat (C : SCat) (p : Obj (composableMorphismsCat C)) :
      NatIso terminalCat C (targetObj C (compositeOfComposablePair C p))
        (compFunctor terminalCat (funCat intervalCat C) C
          (compFunctor terminalCat (composableMorphismsCat C) (funCat intervalCat C) p
            (pullbackPr2 (funCat intervalCat C) (funCat intervalCat C) C
              (targetFunctor C) (sourceFunctor C)))
          (targetFunctor C)) :=
    sorry

end SCT

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Left-unit endpoint compatibility for Segal composition; Axiom E. -/
  lf_def composeLeftUnitCompat : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      NatIso terminalCat C (targetObj C (identityMorphism C (sourceObj C f)))
        (sourceObj C f) :=
    fun C f => identityMorphismTargetCompat C (sourceObj C f)
  /-- Right-unit endpoint compatibility for Segal composition; Axiom E. -/
  lf_def composeRightUnitCompat : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒
      NatIso terminalCat C (targetObj C f)
        (sourceObj C (identityMorphism C (targetObj C f))) :=
    fun C f => invNatIso terminalCat C
      (sourceObj C (identityMorphism C (targetObj C f))) (targetObj C f)
      (identityMorphismSourceCompat C (targetObj C f))

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Explicit inverse data for an interval-shaped morphism.  The category `Iso(C)` is built from
  this data, while Axiom F supplies the Rezk equivalence for that category.
  -/
  syntax_def InvertibleMorphismData (C : SCat) (f : Functor intervalCat C) : Type u :=
    Σ inv : Functor intervalCat C,
      Σ inv_source : NatIso terminalCat C (sourceObj C inv) (targetObj C f),
        Σ inv_target : NatIso terminalCat C (targetObj C inv) (sourceObj C f),
          Σ left_unit : NatIso intervalCat C
              (composeComposableMorphism C f inv
                (invNatIso terminalCat C (sourceObj C inv) (targetObj C f) inv_source))
              (identityMorphism C (sourceObj C f)),
            NatIso intervalCat C
              (composeComposableMorphism C inv f inv_target)
              (identityMorphism C (targetObj C f))
  syntax_sort_role InvertibleMorphismData : side_structure
  /-- Predicate-like witness that an interval-shaped morphism is invertible.  Book target:
  Definition 1.8.2, before packaging invertible morphisms into `Iso(C)`.
  -/
  syntax_abbrev InvertibleMorphism {C : SCat} (f : Functor intervalCat C) :=
    InvertibleMorphismData C f

namespace SCT

/- Projection API for the invertible-morphism package. -/
internal_defs where
  /-- Chosen inverse arrow of an invertible interval-shaped morphism. -/
  def invertibleMorphismInverse (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) : Functor intervalCat C := sorry
  /-- The inverse arrow starts at the target of the original morphism. -/
  def invertibleMorphismInverseSource (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso terminalCat C (sourceObj C (invertibleMorphismInverse C f h)) (targetObj C f) := sorry
  /-- The inverse arrow ends at the source of the original morphism. -/
  def invertibleMorphismInverseTarget (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso terminalCat C (targetObj C (invertibleMorphismInverse C f h)) (sourceObj C f) := sorry
  /-- Composing a morphism with its inverse on the right gives the identity at its source. -/
  def invertibleMorphismLeftUnit (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso intervalCat C
      (composeComposableMorphism C f (invertibleMorphismInverse C f h)
        (invNatIso terminalCat C (sourceObj C (invertibleMorphismInverse C f h))
          (targetObj C f) (invertibleMorphismInverseSource C f h)))
      (identityMorphism C (sourceObj C f)) := sorry
  /-- Composing an inverse on the left with the morphism gives the identity at its target. -/
  def invertibleMorphismRightUnit (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso intervalCat C
      (composeComposableMorphism C (invertibleMorphismInverse C f h) f
        (invertibleMorphismInverseTarget C f h))
      (identityMorphism C (targetObj C f)) := sorry

end SCT


namespace SCT

/- Unit and associativity comparisons for the chosen Segal composition are visible coherence
   debt. -/
internal_defs where
  /-- Left unit for the chosen Segal composition; consequence of Axiom E. -/
  def composeLeftUnit (C : SCat) (f : Functor intervalCat C) :
      NatIso intervalCat C
        (composeComposableMorphism C (identityMorphism C (sourceObj C f)) f
          (composeLeftUnitCompat C f))
        f :=
    sorry
  /-- Right unit for the chosen Segal composition; consequence of Axiom E. -/
  def composeRightUnit (C : SCat) (f : Functor intervalCat C) :
      NatIso intervalCat C
        (composeComposableMorphism C f (identityMorphism C (targetObj C f))
          (composeRightUnitCompat C f))
        f :=
    sorry
  /-- Associativity for Segal composition with explicit endpoint coherences. -/
  def composeAssoc (C : SCat)
      (f : Functor intervalCat C) (g : Functor intervalCat C) (h : Functor intervalCat C)
      (α : NatIso terminalCat C (targetObj C f) (sourceObj C g))
      (β : NatIso terminalCat C (targetObj C g) (sourceObj C h))
      (γL : NatIso terminalCat C
        (targetObj C (composeComposableMorphism C f g α)) (sourceObj C h))
      (γR : NatIso terminalCat C
        (targetObj C f) (sourceObj C (composeComposableMorphism C g h β))) :
      NatIso intervalCat C
        (composeComposableMorphism C (composeComposableMorphism C f g α) h γL)
        (composeComposableMorphism C f (composeComposableMorphism C g h β) γR) :=
    sorry

end SCT
