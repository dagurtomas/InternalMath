/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter3.OverJoinSlice

/-!
# Chapter 4 Axiom K: synthetic categories in context

This file records contextual versions of the SCT vocabulary and constructions.

Book guide, paraphrasing the May 2026 draft:

- Axiom K.1 supplies categories, functors, natural isomorphisms, and equivalences in a fixed
  context. See `ContextCat`, `ContextFunctor`, `ContextNatIso`, `ContextCatEquiv`, and the
  contextual identity, composition, unitor, associator, whiskering, and equivalence projections.
- Axiom K.2 says the underlined axioms hold in any context and all axioms hold in groupoidal
  contexts. The arbitrary-context finite constructions include `contextTerminalCat`,
  `contextInitialCat`, `contextProdCat`, `contextCoprodCat`, and `contextPullbackCat`. The
  groupoidal-context constructions include `contextFunCat`, `contextCoreCat`,
  `contextSubcategory`, `contextLocalization`, `contextGeometricRealization`, `contextJoinCat`,
  and `contextSliceCat`.
- Axiom K.3 gives weakening and reindexing. See `weakenContextCat`, `weakenContextFunctor`,
  `reindexContextCat`, `reindexContextFunctor`, `reindexId`, and `reindexComp`.
- Axiom K.4 gives dependent sums in context. The key declarations are `sigmaCat`, `sigmaPair`,
  `sigmaTranspose`, `sigmaTransposeBeta`, `sigmaTransposeUniq`, `sigmaProjection`, and `sigmaLift`.
- Axiom K.5 says `Σ_Γ *` is equivalent to `Γ`; the split data is `sigmaTerminalUnit`,
  `sigmaTerminalCounit`, and `sigmaTerminalEquiv`.
- Axiom K.6 states compatibility of dependent sums with pullback/reindexing; this file records the
  split data as `sigmaReindexPullbackEquiv`, `sigmaFunctorPullbackSquare`,
  `sigmaSecondProjectionPullbackSquare`, and `sigmaPreservesPullbackEquiv`.
-/

@[expose] public section

/-- Chapter 4: synthetic categories in context and dependent sums; Axiom K. -/
extend_type_theory SCT where

  model_section Chapter4


  /-- Category in context `Γ`; Axiom K.1. -/
  syntax_sort ContextCat (Γ : SCat) : Type (u+1)
  /-- Functor in a fixed context; Axiom K.1. -/
  syntax_sort ContextFunctor {Γ : SCat} (C : ContextCat Γ) (D : ContextCat Γ) : Type u
  /-- Natural isomorphism in context; Axiom K.1. -/
  syntax_sort ContextNatIso {Γ : SCat} {C : ContextCat Γ} {D : ContextCat Γ}
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ C D) : Type u
  /-- Equivalence in context; Axiom K.1. -/
  syntax_sort ContextCatEquiv {Γ : SCat} (C : ContextCat Γ) (D : ContextCat Γ) : Type u
  /-- Pullback-square predicate in a fixed context.  Book context: Chapter 4 of the SCT book. -/
  syntax_sort ContextPullbackSquare {Γ : SCat}
    {A : ContextCat Γ} {B : ContextCat Γ} {C : ContextCat Γ} {D : ContextCat Γ}
    (top : ContextFunctor Γ A B) (left : ContextFunctor Γ A C)
    (right : ContextFunctor Γ B D) (bottom : ContextFunctor Γ C D) : Type u
  /-- Identity contextual functor; Axiom K.1. -/
  lf_opaque idContextFunctor (Γ : SCat) (C : ContextCat Γ) : ContextFunctor Γ C C
  /-- Composition of contextual functors; Axiom K.1. -/
  lf_opaque compContextFunctor (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ D E) : ContextFunctor Γ C E
  /-- Identity contextual natural isomorphism; Axiom K.1. -/
  lf_opaque idContextNatIso (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) : ContextNatIso Γ C D F F
  /-- Composition of contextual natural isomorphisms; Axiom K.1. -/
  lf_opaque compContextNatIso (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ C D)
    (H : ContextFunctor Γ C D) (α : ContextNatIso Γ C D F G)
    (β : ContextNatIso Γ C D G H) : ContextNatIso Γ C D F H
  /-- Inverse contextual natural isomorphism; Axiom K.1. -/
  lf_opaque invContextNatIso (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ C D)
    (α : ContextNatIso Γ C D F G) : ContextNatIso Γ C D G F
  /-- Left unitor for contextual functor composition; Axiom K.1. -/
  lf_opaque contextLeftUnitor (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) :
    ContextNatIso Γ C D (compContextFunctor Γ C C D (idContextFunctor Γ C) F) F
  /-- Right unitor for contextual functor composition; Axiom K.1. -/
  lf_opaque contextRightUnitor (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) :
    ContextNatIso Γ C D (compContextFunctor Γ C D D F (idContextFunctor Γ D)) F
  /-- Associator for contextual functor composition; Axiom K.1. -/
  lf_opaque contextAssocFunctor (Γ : SCat)
    (A : ContextCat Γ) (B : ContextCat Γ) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ A B) (G : ContextFunctor Γ B C) (H : ContextFunctor Γ C D) :
    ContextNatIso Γ A D
      (compContextFunctor Γ A C D (compContextFunctor Γ A B C F G) H)
      (compContextFunctor Γ A B D F (compContextFunctor Γ B C D G H))
  /-- Horizontal composition of contextual natural isomorphisms; Axiom K.1. -/
  lf_opaque contextHorizCompNatIso (Γ : SCat)
    (A : ContextCat Γ) (B : ContextCat Γ) (C : ContextCat Γ)
    (F : ContextFunctor Γ A B) (G : ContextFunctor Γ A B)
    (H : ContextFunctor Γ B C) (K : ContextFunctor Γ B C)
    (α : ContextNatIso Γ A B F G) (β : ContextNatIso Γ B C H K) :
    ContextNatIso Γ A C (compContextFunctor Γ A B C F H)
      (compContextFunctor Γ A B C G K)
  /-- Packaging of contextual equivalence data; Axiom K.1. -/
  lf_opaque contextCatEquivOfData (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ D C)
    (η : ContextNatIso Γ C C (compContextFunctor Γ C D C F G)
      (idContextFunctor Γ C))
    (ε : ContextNatIso Γ D D (compContextFunctor Γ D C D G F)
      (idContextFunctor Γ D)) : ContextCatEquiv Γ C D
  /-- Forward contextual functor of an equivalence; Axiom K.1. -/
  lf_opaque contextCatEquivForward (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (e : ContextCatEquiv Γ C D) : ContextFunctor Γ C D
  /-- Backward contextual functor of an equivalence; Axiom K.1. -/
  lf_opaque contextCatEquivBackward (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (e : ContextCatEquiv Γ C D) : ContextFunctor Γ D C
  /-- Unit of a contextual equivalence; Axiom K.1. -/
  lf_opaque contextCatEquivUnit (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (e : ContextCatEquiv Γ C D) :
    ContextNatIso Γ C C
      (compContextFunctor Γ C D C
        (contextCatEquivForward Γ C D e) (contextCatEquivBackward Γ C D e))
      (idContextFunctor Γ C)
  /-- Counit of a contextual equivalence; Axiom K.1. -/
  lf_opaque contextCatEquivCounit (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (e : ContextCatEquiv Γ C D) :
    ContextNatIso Γ D D
      (compContextFunctor Γ D C D
        (contextCatEquivBackward Γ C D e) (contextCatEquivForward Γ C D e))
      (idContextFunctor Γ D)

  /-- Evidence that a context is groupoidal; Axiom K.2. -/
  syntax_sort GroupoidalContext (Γ : SCat) : Type u
  /-- Every anima underlies a groupoidal context; Axiom K.2. -/
  lf_opaque groupoidalContextOfAnima (A : Anima) : GroupoidalContext (animaCat A)
  /-- Every groupoid gives a groupoidal context; Axiom K.2. -/
  lf_opaque groupoidalContextOfGroupoid (Γ : SCat) (gΓ : GroupoidWitness Γ) : GroupoidalContext Γ

  /-- Weakening of an absolute category to a context; Axiom K.3. -/
  lf_opaque weakenContextCat (Γ : SCat) (C : SCat) : ContextCat Γ
  /-- Weakening of an absolute functor to a context; Axiom K.3. -/
  lf_opaque weakenContextFunctor (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor C D) : ContextFunctor Γ (weakenContextCat Γ C) (weakenContextCat Γ D)
  /-- Weakening of an absolute natural isomorphism to a context; Axiom K.3. -/
  lf_opaque weakenContextNatIso (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor C D) (G : Functor C D) (α : NatIso F G) :
    ContextNatIso Γ (weakenContextCat Γ C) (weakenContextCat Γ D)
      (weakenContextFunctor Γ C D F) (weakenContextFunctor Γ C D G)
  /-- Weakening of an absolute equivalence to a context; Axiom K.3. -/
  lf_opaque weakenContextCatEquiv (Γ : SCat) (C : SCat) (D : SCat)
    (e : CatEquiv C D) : ContextCatEquiv Γ (weakenContextCat Γ C)
      (weakenContextCat Γ D)
  /-- Reindexing of contextual categories; Axiom K.3. -/
  lf_opaque reindexContextCat (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) : ContextCat Δ
  /-- Reindexing of contextual functors; Axiom K.3. -/
  lf_opaque reindexContextFunctor (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) (D : ContextCat Γ) (F : ContextFunctor Γ C D) :
    ContextFunctor Δ (reindexContextCat Δ Γ u C) (reindexContextCat Δ Γ u D)
  /-- Reindexing of contextual natural isomorphisms; Axiom K.3. -/
  lf_opaque reindexContextNatIso (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ C D)
    (α : ContextNatIso Γ C D F G) :
    ContextNatIso Δ (reindexContextCat Δ Γ u C) (reindexContextCat Δ Γ u D)
      (reindexContextFunctor Δ Γ u C D F) (reindexContextFunctor Δ Γ u C D G)
  /-- Reindexing of contextual equivalences; Axiom K.3. -/
  lf_opaque reindexContextCatEquiv (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) (D : ContextCat Γ) (e : ContextCatEquiv Γ C D) :
    ContextCatEquiv Δ (reindexContextCat Δ Γ u C) (reindexContextCat Δ Γ u D)
  /-- Reindexing along the identity functor is equivalent to doing nothing; Axiom K.3. -/
  lf_opaque reindexContextCatId (Γ : SCat) (C : ContextCat Γ) :
    ContextCatEquiv Γ (reindexContextCat Γ Γ (idFunctor Γ) C) C
  /-- Reindexing along a composite is equivalent to iterated reindexing; Axiom K.3. -/
  lf_opaque reindexContextCatComp (Θ : SCat) (Δ : SCat) (Γ : SCat)
    (v : Functor Θ Δ) (u : Functor Δ Γ) (C : ContextCat Γ) :
    ContextCatEquiv Θ
      (reindexContextCat Θ Γ (compFunctor v u) C)
      (reindexContextCat Θ Δ v (reindexContextCat Δ Γ u C))

  /-- Contextual terminal category, available in arbitrary contexts; Axiom K.2. -/
  lf_opaque contextTerminalCat (Γ : SCat) : ContextCat Γ
  /-- Contextual initial category, available in arbitrary contexts; Axiom K.2. -/
  lf_opaque contextInitialCat (Γ : SCat) : ContextCat Γ

  /-- Contextual binary products, available in arbitrary contexts; Axiom K.2. -/
  lf_opaque contextProdCat (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextCat Γ

  /-- Unique map to the contextual terminal category; Axiom K.2 data. -/
  lf_opaque contextTerminalProjection (Γ : SCat) (C : ContextCat Γ) :
    ContextFunctor Γ C (contextTerminalCat Γ)
  /-- Unique map out of the contextual initial category; Axiom K.2 data. -/
  lf_opaque contextInitialElim (Γ : SCat) (C : ContextCat Γ) :
    ContextFunctor Γ (contextInitialCat Γ) C

extend_type_theory SCT where

  model_section Chapter4

  /-- First contextual product projection; Axiom K.2. -/
  lf_opaque contextProdPr1 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextFunctor Γ (contextProdCat Γ C D) C
  /-- Second contextual product projection; Axiom K.2. -/
  lf_opaque contextProdPr2 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextFunctor Γ (contextProdCat Γ C D) D
  /-- Contextual binary coproducts, available in arbitrary contexts; Axiom K.2. -/
  lf_opaque contextCoprodCat (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextCat Γ

  /-- Contextual product pairing; Axiom K.2 data. -/
  lf_opaque contextProdPair (Γ : SCat) (X : ContextCat Γ)
    (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ X C) (G : ContextFunctor Γ X D) :
    ContextFunctor Γ X (contextProdCat Γ C D)
  /-- First contextual product β comparison; Axiom K.2 data. -/
  lf_opaque contextProdBeta1 (Γ : SCat) (X : ContextCat Γ)
    (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ X C) (G : ContextFunctor Γ X D) :
    ContextNatIso Γ X C
      (compContextFunctor Γ X (contextProdCat Γ C D) C
        (contextProdPair Γ X C D F G) (contextProdPr1 Γ C D)) F
  /-- Second contextual product β comparison; Axiom K.2 data. -/
  lf_opaque contextProdBeta2 (Γ : SCat) (X : ContextCat Γ)
    (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ X C) (G : ContextFunctor Γ X D) :
    ContextNatIso Γ X D
      (compContextFunctor Γ X (contextProdCat Γ C D) D
        (contextProdPair Γ X C D F G) (contextProdPr2 Γ C D)) G

extend_type_theory SCT where

  model_section Chapter4

  /-- First contextual coproduct injection; Axiom K.2. -/
  lf_opaque contextCoprodIn1 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextFunctor Γ C (contextCoprodCat Γ C D)
  /-- Second contextual coproduct injection; Axiom K.2. -/
  lf_opaque contextCoprodIn2 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) :
    ContextFunctor Γ D (contextCoprodCat Γ C D)
  /-- Contextual pullbacks, available in arbitrary contexts; Axiom K.2. -/
  lf_opaque contextPullbackCat (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C E) (G : ContextFunctor Γ D E) : ContextCat Γ

  /-- Contextual coproduct case analysis; Axiom K.2 data. -/
  lf_opaque contextCoprodCase (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (X : ContextCat Γ) (F : ContextFunctor Γ C X) (G : ContextFunctor Γ D X) :
    ContextFunctor Γ (contextCoprodCat Γ C D) X
  /-- First contextual coproduct β comparison; Axiom K.2 data. -/
  lf_opaque contextCoprodBeta1 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (X : ContextCat Γ) (F : ContextFunctor Γ C X) (G : ContextFunctor Γ D X) :
    ContextNatIso Γ C X
      (compContextFunctor Γ C (contextCoprodCat Γ C D) X
        (contextCoprodIn1 Γ C D) (contextCoprodCase Γ C D X F G)) F
  /-- Second contextual coproduct β comparison; Axiom K.2 data. -/
  lf_opaque contextCoprodBeta2 (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (X : ContextCat Γ) (F : ContextFunctor Γ C X) (G : ContextFunctor Γ D X) :
    ContextNatIso Γ D X
      (compContextFunctor Γ D (contextCoprodCat Γ C D) X
        (contextCoprodIn2 Γ C D) (contextCoprodCase Γ C D X F G)) G

extend_type_theory SCT where

  model_section Chapter4

  /-- Contextual functor categories in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextFunCat (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (D : ContextCat Γ) : ContextCat Γ

  /-- First contextual pullback projection; Axiom K.2 data. -/
  lf_opaque contextPullbackPr1 (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C E) (G : ContextFunctor Γ D E) :
    ContextFunctor Γ (contextPullbackCat Γ C D E F G) C
  /-- Second contextual pullback projection; Axiom K.2 data. -/
  lf_opaque contextPullbackPr2 (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C E) (G : ContextFunctor Γ D E) :
    ContextFunctor Γ (contextPullbackCat Γ C D E F G) D
  /-- Contextual pullback commutativity; Axiom K.2 data. -/
  lf_opaque contextPullbackComm (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C E) (G : ContextFunctor Γ D E) :
    ContextNatIso Γ (contextPullbackCat Γ C D E F G) E
      (compContextFunctor Γ (contextPullbackCat Γ C D E F G) C E
        (contextPullbackPr1 Γ C D E F G) F)
      (compContextFunctor Γ (contextPullbackCat Γ C D E F G) D E
        (contextPullbackPr2 Γ C D E F G) G)

extend_type_theory SCT where

  model_section Chapter4

  /-- Contextual groupoid cores in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextCoreCat (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : ContextCat Γ
  /-- Contextual morphism collection in a groupoidal context.  Book context: Chapter 4 of the SCT
  book.
  -/
  syntax_sort ContextMorphismCollection {Γ : SCat} (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : Type (u+1)
  /-- Contextual object collection in a groupoidal context.
  Book context:Chapter 4 of the SCT book.
  -/
  syntax_sort ContextObjectCollection {Γ : SCat} (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : Type (u+1)
  /-- Contextual subcategories in groupoidal contexts; Axiom K.2 applies Axiom H in groupoidal
  context. -/
  lf_opaque contextSubcategory (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (W : ContextMorphismCollection Γ gΓ C) : ContextCat Γ
  /-- Contextual localizations in groupoidal contexts; Axiom K.2 applies Axiom I in groupoidal
  context. -/
  lf_opaque contextLocalization (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (W : ContextMorphismCollection Γ gΓ C) : ContextCat Γ
  /-- Contextual geometric realizations in groupoidal contexts; Axiom K.2 applies Axiom J in
  groupoidal context. -/
  lf_opaque contextGeometricRealization (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : ContextCat Γ
  /-- Contextual joins in groupoidal contexts; Axiom K.2 applies Axiom J.1/J.2 in groupoidal
  context. -/
  lf_opaque contextJoinCat (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (D : ContextCat Γ) : ContextCat Γ
  /-- Contextual slice categories in groupoidal contexts; Axiom K.2 applies the Chapter 3 slice
  construction in groupoidal context. -/
  lf_opaque contextSliceCat (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (A : ContextCat Γ) (C : ContextCat Γ) (F : ContextFunctor Γ A C) : ContextCat Γ

  /-- Dependent sum of a category in context; Axiom K.4. -/
  lf_opaque sigmaCat (Γ : SCat) (C : ContextCat Γ) : SCat
  /-- Pair functor `(γ,-) : C(γ) → w_Γ(Σ_Γ C)` in context `Γ`; Axiom K.4. -/
  lf_opaque sigmaPair (Γ : SCat) (C : ContextCat Γ) :
    ContextFunctor Γ C (weakenContextCat Γ (sigmaCat Γ C))
  /-- Universal transpose from contextual maps into weakenings; Axiom K.4. -/
  lf_opaque sigmaDesc (Γ : SCat) (C : ContextCat Γ) (D : SCat)
    (F : ContextFunctor Γ C (weakenContextCat Γ D)) : Functor (sigmaCat Γ C) D
  /-- β comparison for dependent-sum transposition; Axiom K.4. -/
  lf_opaque sigmaDescBeta (Γ : SCat) (C : ContextCat Γ) (D : SCat)
    (F : ContextFunctor Γ C (weakenContextCat Γ D)) :
    ContextNatIso Γ C (weakenContextCat Γ D)
      (compContextFunctor Γ C (weakenContextCat Γ (sigmaCat Γ C))
        (weakenContextCat Γ D) (sigmaPair Γ C)
        (weakenContextFunctor Γ (sigmaCat Γ C) D (sigmaDesc Γ C D F))) F
  /-- Uniqueness for dependent-sum transposition; Axiom K.4. -/
  lf_opaque sigmaDescUniq (Γ : SCat) (C : ContextCat Γ) (D : SCat)
    (F : ContextFunctor Γ C (weakenContextCat Γ D)) (G : Functor (sigmaCat Γ C) D)
    (β : ContextNatIso Γ C (weakenContextCat Γ D)
      (compContextFunctor Γ C (weakenContextCat Γ (sigmaCat Γ C))
        (weakenContextCat Γ D) (sigmaPair Γ C) (weakenContextFunctor Γ (sigmaCat Γ C) D G)) F) :
    NatIso (sigmaCat Γ C) D G (sigmaDesc Γ C D F)
  /-- Projection from a dependent sum; Axiom K.4. -/
  lf_opaque sigmaProjection (Γ : SCat) (C : ContextCat Γ) : Functor (sigmaCat Γ C) Γ
  /-- Pairing/lift into a dependent sum; Axiom K.4. -/
  lf_opaque sigmaLift (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) : Functor Δ (sigmaCat Γ C)
  /-- Dependent sum is functorial in contextual functors, by the dependent-sum universal property.
  Book context: Chapter 4 of the SCT book.
  -/
  lf_def sigmaFunctor : (Γ : SCat) ⇒ (C : ContextCat Γ) ⇒ (D : ContextCat Γ) ⇒
      ContextFunctor Γ C D ⇒ Functor (sigmaCat Γ C) (sigmaCat Γ D) :=
    fun Γ C D F => sigmaDesc Γ C (sigmaCat Γ D)
      (compContextFunctor Γ C D (weakenContextCat Γ (sigmaCat Γ D)) F (sigmaPair Γ D))
  /-- Functoriality square for dependent sums commutes in context.  Book context: Chapter 4 of the
  SCT book.
  -/
  lf_def sigmaFunctorBeta : (Γ : SCat) ⇒ (C : ContextCat Γ) ⇒ (D : ContextCat Γ) ⇒
      (F : ContextFunctor Γ C D) ⇒
        ContextNatIso Γ C (weakenContextCat Γ (sigmaCat Γ D))
          (compContextFunctor Γ C (weakenContextCat Γ (sigmaCat Γ C))
            (weakenContextCat Γ (sigmaCat Γ D)) (sigmaPair Γ C)
            (weakenContextFunctor Γ (sigmaCat Γ C) (sigmaCat Γ D) (sigmaFunctor Γ C D F)))
          (compContextFunctor Γ C D (weakenContextCat Γ (sigmaCat Γ D)) F (sigmaPair Γ D)) :=
    fun Γ C D F => sigmaDescBeta Γ C (sigmaCat Γ D)
      (compContextFunctor Γ C D (weakenContextCat Γ (sigmaCat Γ D)) F (sigmaPair Γ D))

extend_type_theory SCT where

  model_section Chapter4

  /-- Unit for `Σ_Γ * → Γ`; Axiom K.5 split equivalence data. -/
  lf_opaque sigmaTerminalUnit (Γ : SCat) :
    NatIso (sigmaCat Γ (weakenContextCat Γ terminalCat))
      (sigmaCat Γ (weakenContextCat Γ terminalCat))
      (compFunctor (sigmaCat Γ (weakenContextCat Γ terminalCat)) Γ
        (sigmaCat Γ (weakenContextCat Γ terminalCat))
        (sigmaProjection Γ (weakenContextCat Γ terminalCat))
        (sigmaLift Γ Γ (idFunctor Γ) (weakenContextCat Γ terminalCat)))
      (idFunctor (sigmaCat Γ (weakenContextCat Γ terminalCat)))
  /-- Counit for `Σ_Γ * → Γ`; Axiom K.5 split equivalence data. -/
  lf_opaque sigmaTerminalCounit (Γ : SCat) :
    NatIso (compFunctor Γ (sigmaCat Γ (weakenContextCat Γ terminalCat)) Γ
        (sigmaLift Γ Γ (idFunctor Γ) (weakenContextCat Γ terminalCat))
        (sigmaProjection Γ (weakenContextCat Γ terminalCat))) (idFunctor Γ)

extend_type_theory SCT where

  model_section Chapter4


  /-- `Σ_Γ * → Γ` is an equivalence; Axiom K.5. -/
  lf_def sigma_terminal_equiv :
      (Γ : SCat) ⇒ CatEquiv (sigmaCat Γ (weakenContextCat Γ terminalCat)) Γ :=
    fun Γ => catEquivOfData (sigmaCat Γ (weakenContextCat Γ terminalCat)) Γ
      (sigmaProjection Γ (weakenContextCat Γ terminalCat))
      (sigmaLift Γ Γ (idFunctor Γ) (weakenContextCat Γ terminalCat))
      (sigmaTerminalUnit Γ) (sigmaTerminalCounit Γ)
  /-- Second projection `Σ_Γ w_Γ D → D`, obtained by transposing the identity in context.  Book
  context: Chapter 4 of the SCT book.
  -/
  lf_def sigmaSecondProjection : (Γ : SCat) ⇒ (D : SCat) ⇒
      Functor (sigmaCat Γ (weakenContextCat Γ D)) D :=
    fun Γ D => sigmaDesc Γ (weakenContextCat Γ D) D
      (idContextFunctor Γ (weakenContextCat Γ D))

extend_type_theory SCT where

  model_section Chapter4

  /-- Dependent sums commute with reindexing by pullback; Axiom K.6 split data. -/
  lf_opaque sigmaReindexPullbackEquiv (Δ : SCat) (Γ : SCat) (u : Functor Δ Γ)
    (C : ContextCat Γ) :
    CatEquiv (sigmaCat Δ (reindexContextCat Δ Γ u C))
      (pullbackCat Δ (sigmaCat Γ C) Γ u (sigmaProjection Γ C))
  /-- K.6 first pullback clause for a contextual functor and pair functors. -/
  lf_opaque sigmaFunctorPullbackSquare (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) :
    ContextPullbackSquare Γ C (weakenContextCat Γ (sigmaCat Γ C)) D
      (weakenContextCat Γ (sigmaCat Γ D)) (sigmaPair Γ C) F
      (weakenContextFunctor Γ (sigmaCat Γ C) (sigmaCat Γ D) (sigmaFunctor Γ C D F))
      (sigmaPair Γ D)

extend_type_theory SCT where

  model_section Chapter4


  /-- Category over `Γ` associated to a contextual category.  Book context: Chapter 4 of the SCT
  book.
  -/
  lf_def contextToOverFunctor : (Γ : SCat) ⇒ (C : ContextCat Γ) ⇒ Functor (sigmaCat Γ C) Γ :=
    fun Γ C => sigmaProjection Γ C

extend_type_theory SCT where

  model_section Chapter4

  /-- K.6 second-projection pullback clause for weakened absolute functors. -/
  lf_opaque sigmaSecondProjectionPullbackSquare (Γ : SCat) (D : SCat) (E : SCat)
    (F : Functor D E) :
    PullbackSquare (sigmaCat Γ (weakenContextCat Γ D)) D
      (sigmaCat Γ (weakenContextCat Γ E)) E (sigmaSecondProjection Γ D)
      (sigmaFunctor Γ (weakenContextCat Γ D) (weakenContextCat Γ E)
        (weakenContextFunctor Γ D E F)) F (sigmaSecondProjection Γ E)
  /-- K.6 preservation of contextual pullbacks by dependent sums. -/
  lf_opaque sigmaPreservesPullbackEquiv (Γ : SCat)
    (C : ContextCat Γ) (D : ContextCat Γ) (E : ContextCat Γ)
    (F : ContextFunctor Γ C E) (G : ContextFunctor Γ D E) :
    CatEquiv (sigmaCat Γ (contextPullbackCat Γ C D E F G))
      (pullbackCat (sigmaCat Γ C) (sigmaCat Γ D) (sigmaCat Γ E)
        (sigmaFunctor Γ C E F) (sigmaFunctor Γ D E G))

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Category of contextual categories over `Γ`, used to state the context/over-category
  equivalence.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence using dependent sums and reindexing. -/
  def contextCategoryCat (Γ : SCat) : SCat := sorry
  /-- Object of `contextCategoryCat Γ` corresponding to a contextual category.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence using dependent sums and reindexing. -/
  def contextCategoryObject (Γ : SCat) (C : ContextCat Γ) : Obj (contextCategoryCat Γ) := sorry

end SCT

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Contextual category associated to a category over `Γ`.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence using dependent sums and reindexing. -/
  def overFunctorToContext (Γ : SCat) (E : SCat) (p : Functor E Γ) : ContextCat Γ := sorry
  /-- Equivalence between contextual categories over `Γ` and categories over `Γ`.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence using dependent sums and reindexing. -/
  def contextOverCorrespondence (Γ : SCat) : CatEquiv (contextCategoryCat Γ) (overCat Γ) := sorry



end SCT
