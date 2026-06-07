/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalLean.Command

/-!
# SCT prelude: Axiom A and the ambient vocabulary

This file opens the InternalLean type theory `SCT`. It introduces the primitive vocabulary used by
all later chapter files. The interface is intrinsic: object sorts contain valid data by
construction, so there are no generic `wf...` judgments. Mathematical properties that are not part
of a sort remain explicit witness sorts or packages.

Book guide, paraphrasing the May 2026 draft:

- Axiom A.1 supplies synthetic categories, functors, natural isomorphisms, mapping anima, and
  families of categories indexed by anima.
- Axiom A.2 identifies terms of a category `C` in context `Γ` with functors `Γ ⟶ C`; absolute
  objects are functors from the terminal category.
- Axiom A.3 supplies identity functors, composition, unitors, associators, whiskering, and
  horizontal composition. These laws are isomorphism data, not strict definitional equalities.
- Axiom A.4 says a category equivalent to an anima is again an anima.

Key declarations below:

- `Anima`, `SCat`, `animaCat`, `isAnimaCat`, `anima_cat_is_anima`,
  `equiv_to_anima_is_anima`;
- `Functor`, `NatTrans`, `ObjectwiseNatIsoData`, `NatIso`, `CatEquiv`, `mapAnima`;
- `AnimaIndexedCat`, `animaIndexedFiber`, `sigmaAnimaIndexed`,
  `sigmaAnimaIndexedProjection`;
- `idFunctor`, `compFunctor`, `idNatIso`, `compNatIso`, `invNatIso`, `leftUnitor`,
  `rightUnitor`, `assocFunctor`, `preWhiskerNatIso`, `postWhiskerNatIso`, and
  `horizCompNatIso`.
-/

@[expose] public section

/--
Book-structured intrinsic SCT. Chapter 1 starts with the naive-category-theory language,
including anima as primitive objects with underlying synthetic categories.
-/
declare_type_theory SCT{u} where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1


  /-- Primitive anima/groupoids; Axioms A.4 and G. -/
  syntax_sort Anima : Type (u+1)
  /-- Primitive synthetic categories; Axiom A.1. -/
  syntax_sort SCat : Type (u+1)
  /-- Underlying synthetic category of an anima; Axioms A.4 and G. -/
  lf_opaque animaCat (A : Anima) : SCat

  /-- Predicate saying that a synthetic category is an anima-category; Axioms A.4 and G. -/
  judgment isAnimaCat (C : SCat)
  judgment_role isAnimaCat : side_judgment

  /-- Every primitive anima determines an anima-category; Axiom A.4. -/
  rule anima_cat_is_anima (A : Anima) where
    conclusion : isAnimaCat (animaCat A)
  /-- Any category equivalent to an anima is an anima; Axiom A.4. -/
  rule equiv_to_anima_is_anima (C : SCat) (A : Anima)
    (e : CatEquiv C (animaCat A)) where
    conclusion : isAnimaCat C

  /-- Functors between synthetic categories; Axiom A.1. -/
  syntax_sort Functor (C : SCat) (D : SCat) : Type u
  /-- Natural transformations between parallel functors; Axioms A.1' and A.2'. -/
  syntax_sort NatTrans {C : SCat} {D : SCat} (F : Functor C D) (G : Functor C D) : Type u
  /-- Componentwise invertibility evidence for a natural transformation. -/
  syntax_def ObjectwiseNatIsoData {C : SCat} {D : SCat}
    (F : Functor C D) (G : Functor C D) (α : NatTrans F G) : Type u := sorry
  syntax_sort_role ObjectwiseNatIsoData : side_structure
  /-- Objectwise natural-isomorphism evidence for a natural transformation. -/
  syntax_abbrev ObjectwiseNatIso {C : SCat} {D : SCat}
    (F : Functor C D) (G : Functor C D) (α : NatTrans F G) :=
    ObjectwiseNatIsoData F G α
  /-- Natural-isomorphism/coherence data between parallel functors; Axiom A.1.
  The package exposes its underlying natural transformation and objectwise invertibility witness.
  -/
  syntax_abbrev NatIso {C : SCat} {D : SCat} (F : Functor C D) (G : Functor C D) :=
    Σ natIsoTrans : NatTrans F G, ObjectwiseNatIso F G natIsoTrans
  /-- Category equivalence data; definition after Axiom A.3. -/
  syntax_sort CatEquiv (C : SCat) (D : SCat) : Type u
  /-- The mapping anima `Map(C,D)` whose terms are functors `C → D`; Axiom A.1(4). -/
  lf_opaque mapAnima (C : SCat) (D : SCat) : Anima
  /-- A family of synthetic categories indexed by an anima; Axiom A.1(3). -/
  syntax_sort AnimaIndexedCat (Γ : Anima) : Type (u+1)
  /-- Fiber of an anima-indexed family at an object of the indexing anima.  Book context: Chapter 1
  of the SCT book.
  -/
  lf_opaque animaIndexedFiber (Γ : Anima) (C : AnimaIndexedCat Γ)
    (x : Obj (animaCat Γ)) : SCat
  /-- Dependent sum of an anima-indexed family of synthetic categories; Axiom A.1(3). -/
  lf_opaque sigmaAnimaIndexed (Γ : Anima) (C : AnimaIndexedCat Γ) : SCat
  /-- First projection from an anima-indexed dependent sum.
  Book context:Chapter 1 of the SCT book.
  -/
  lf_opaque sigmaAnimaIndexedProjection (Γ : Anima) (C : AnimaIndexedCat Γ) :
    Functor (sigmaAnimaIndexed Γ C) (animaCat Γ)
  /-- Identity functor; Axiom A.3. -/
  lf_opaque idFunctor (C : SCat) : Functor C C
  /-- Composition of functors; Axiom A.3. -/
  lf_opaque compFunctor {C : SCat} {D : SCat} {E : SCat}
    (F : Functor C D) (G : Functor D E) : Functor C E
  /-- Identity natural isomorphism; Axioms A.1' and A.2'. -/
  lf_opaque idNatIso {C : SCat} {D : SCat} (F : Functor C D) : NatIso F F
  /-- Vertical composition of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque compNatIso {C : SCat} {D : SCat} {F : Functor C D} {G : Functor C D}
    {H : Functor C D} (α : NatIso F G) (β : NatIso G H) : NatIso F H
  /-- Inverse natural isomorphism; Axiom A.1. -/
  lf_opaque invNatIso {C : SCat} {D : SCat} {F : Functor C D} {G : Functor C D}
    (α : NatIso F G) : NatIso G F
  /-- Left unitor for functor composition; Axiom A.3. -/
  lf_opaque leftUnitor {C : SCat} {D : SCat} (F : Functor C D) :
    NatIso (compFunctor (idFunctor C) F) F
  /-- Right unitor for functor composition; Axiom A.3. -/
  lf_opaque rightUnitor {C : SCat} {D : SCat} (F : Functor C D) :
    NatIso (compFunctor F (idFunctor D)) F
  /-- Associator for functor composition; Axiom A.3. -/
  lf_opaque assocFunctor {B : SCat} {C : SCat} {D : SCat} {E : SCat}
    (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    NatIso (compFunctor (compFunctor F G) H) (compFunctor F (compFunctor G H))
  /-- Inverse associator, derived from the associator; Axiom A.3. -/
  lf_def assocFunctorInv : (B : SCat) ⇒ (C : SCat) ⇒ (D : SCat) ⇒ (E : SCat) ⇒
      (F : Functor B C) ⇒ (G : Functor C D) ⇒ (H : Functor D E) ⇒
        NatIso (compFunctor F (compFunctor G H)) (compFunctor (compFunctor F G) H) :=
    fun B C D E F G H => invNatIso (assocFunctor B C D E F G H)
  /-- Pre-whiskering of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque preWhiskerNatIso {B : SCat} {C : SCat} {D : SCat}
    (K : Functor B C) {F : Functor C D} {G : Functor C D}
    (α : NatIso F G) :
    NatIso (compFunctor K F) (compFunctor K G)
  /-- Post-whiskering of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque postWhiskerNatIso {B : SCat} {C : SCat} {D : SCat}
    {F : Functor B C} {G : Functor B C} (K : Functor C D)
    (α : NatIso F G) :
    NatIso (compFunctor F K) (compFunctor G K)
  /-- Horizontal composition of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque horizCompNatIso {B : SCat} {C : SCat} {D : SCat}
    {F : Functor B C} {G : Functor B C} {H : Functor C D} {K : Functor C D}
    (α : NatIso F G) (β : NatIso H K) :
    NatIso (compFunctor F H) (compFunctor G K)
  /-- Packaging of equivalence data; definition after Axiom A.3. -/
  lf_opaque catEquivOfData {C : SCat} {D : SCat} (F : Functor C D) (G : Functor D C)
    (η : NatIso (compFunctor F G) (idFunctor C))
    (ε : NatIso (compFunctor G F) (idFunctor D)) : CatEquiv C D
  /-- Forward functor of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivForward {C : SCat} {D : SCat} (e : CatEquiv C D) : Functor C D
  /-- Backward functor of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivBackward {C : SCat} {D : SCat} (e : CatEquiv C D) : Functor D C
  /-- Unit natural isomorphism of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivUnit {C : SCat} {D : SCat} (e : CatEquiv C D) :
    NatIso (compFunctor (catEquivForward e) (catEquivBackward e)) (idFunctor C)
  /-- Counit natural isomorphism of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivCounit {C : SCat} {D : SCat} (e : CatEquiv C D) :
    NatIso (compFunctor (catEquivBackward e) (catEquivForward e)) (idFunctor D)
  /-- Reflexivity of category equivalence, packaged from identity functors and unitors.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_def catEquivRefl : (C : SCat) ⇒ CatEquiv C C :=
    fun C => catEquivOfData C C (idFunctor C) (idFunctor C)
      (rightUnitor C C (idFunctor C)) (rightUnitor C C (idFunctor C))
  /-- Symmetry of category equivalence, packaged from inverse/unit/counit data.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_def catEquivSymm : (C : SCat) ⇒ (D : SCat) ⇒ CatEquiv C D ⇒ CatEquiv D C :=
    fun C D e => catEquivOfData D C
      (catEquivBackward C D e) (catEquivForward C D e)
      (catEquivCounit C D e) (catEquivUnit C D e)
  /-- Unit comparison for composition of equivalences, derived from associativity, whiskering, and
  the two input units.  Book target: §1.1.3, transitivity after Definition 1.1.9. -/
  lf_def catEquivTransUnit : (A : SCat) ⇒ (B : SCat) ⇒ (C : SCat) ⇒
      (eAB : CatEquiv A B) ⇒ (eBC : CatEquiv B C) ⇒
      NatIso A A
        (compFunctor A C A
          (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC))
          (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB)))
        (idFunctor A) :=
    fun A B C eAB eBC =>
      compNatIso A A
        (compFunctor A C A
          (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC))
          (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB)))
        (compFunctor A B A (catEquivForward A B eAB)
          (compFunctor B C A (catEquivForward B C eBC)
            (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB))))
        (idFunctor A)
        (assocFunctor A B C A
          (catEquivForward A B eAB) (catEquivForward B C eBC)
          (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB)))
        (compNatIso A A
          (compFunctor A B A (catEquivForward A B eAB)
            (compFunctor B C A (catEquivForward B C eBC)
              (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB))))
          (compFunctor A B A (catEquivForward A B eAB)
            (compFunctor B B A
              (compFunctor B C B (catEquivForward B C eBC) (catEquivBackward B C eBC))
              (catEquivBackward A B eAB)))
          (idFunctor A)
          (preWhiskerNatIso A B A (catEquivForward A B eAB)
            (compFunctor B C A (catEquivForward B C eBC)
              (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB)))
            (compFunctor B B A
              (compFunctor B C B (catEquivForward B C eBC) (catEquivBackward B C eBC))
              (catEquivBackward A B eAB))
            (assocFunctorInv B C B A
              (catEquivForward B C eBC) (catEquivBackward B C eBC)
              (catEquivBackward A B eAB)))
          (compNatIso A A
            (compFunctor A B A (catEquivForward A B eAB)
              (compFunctor B B A
                (compFunctor B C B (catEquivForward B C eBC) (catEquivBackward B C eBC))
                (catEquivBackward A B eAB)))
            (compFunctor A B A (catEquivForward A B eAB)
              (compFunctor B B A (idFunctor B) (catEquivBackward A B eAB)))
            (idFunctor A)
            (preWhiskerNatIso A B A (catEquivForward A B eAB)
              (compFunctor B B A
                (compFunctor B C B (catEquivForward B C eBC) (catEquivBackward B C eBC))
                (catEquivBackward A B eAB))
              (compFunctor B B A (idFunctor B) (catEquivBackward A B eAB))
              (postWhiskerNatIso B B A
                (compFunctor B C B (catEquivForward B C eBC) (catEquivBackward B C eBC))
                (idFunctor B) (catEquivBackward A B eAB)
                (catEquivUnit B C eBC)))
            (compNatIso A A
              (compFunctor A B A (catEquivForward A B eAB)
                (compFunctor B B A (idFunctor B) (catEquivBackward A B eAB)))
              (compFunctor A B A (catEquivForward A B eAB) (catEquivBackward A B eAB))
              (idFunctor A)
              (preWhiskerNatIso A B A (catEquivForward A B eAB)
                (compFunctor B B A (idFunctor B) (catEquivBackward A B eAB))
                (catEquivBackward A B eAB)
                (leftUnitor B A (catEquivBackward A B eAB)))
              (catEquivUnit A B eAB))))
  /-- Counit comparison for composition of equivalences, derived from associativity, whiskering,
  and the two input counits.  Book target: §1.1.3, transitivity after Definition 1.1.9. -/
  lf_def catEquivTransCounit : (A : SCat) ⇒ (B : SCat) ⇒ (C : SCat) ⇒
      (eAB : CatEquiv A B) ⇒ (eBC : CatEquiv B C) ⇒
      NatIso C C
        (compFunctor C A C
          (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB))
          (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC)))
        (idFunctor C) :=
    fun A B C eAB eBC =>
      compNatIso C C
        (compFunctor C A C
          (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB))
          (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC)))
        (compFunctor C B C (catEquivBackward B C eBC)
          (compFunctor B A C (catEquivBackward A B eAB)
            (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC))))
        (idFunctor C)
        (assocFunctor C B A C
          (catEquivBackward B C eBC) (catEquivBackward A B eAB)
          (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC)))
        (compNatIso C C
          (compFunctor C B C (catEquivBackward B C eBC)
            (compFunctor B A C (catEquivBackward A B eAB)
              (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC))))
          (compFunctor C B C (catEquivBackward B C eBC)
            (compFunctor B B C
              (compFunctor B A B (catEquivBackward A B eAB) (catEquivForward A B eAB))
              (catEquivForward B C eBC)))
          (idFunctor C)
          (preWhiskerNatIso C B C (catEquivBackward B C eBC)
            (compFunctor B A C (catEquivBackward A B eAB)
              (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC)))
            (compFunctor B B C
              (compFunctor B A B (catEquivBackward A B eAB) (catEquivForward A B eAB))
              (catEquivForward B C eBC))
            (assocFunctorInv B A B C
              (catEquivBackward A B eAB) (catEquivForward A B eAB)
              (catEquivForward B C eBC)))
          (compNatIso C C
            (compFunctor C B C (catEquivBackward B C eBC)
              (compFunctor B B C
                (compFunctor B A B (catEquivBackward A B eAB) (catEquivForward A B eAB))
                (catEquivForward B C eBC)))
            (compFunctor C B C (catEquivBackward B C eBC)
              (compFunctor B B C (idFunctor B) (catEquivForward B C eBC)))
            (idFunctor C)
            (preWhiskerNatIso C B C (catEquivBackward B C eBC)
              (compFunctor B B C
                (compFunctor B A B (catEquivBackward A B eAB) (catEquivForward A B eAB))
                (catEquivForward B C eBC))
              (compFunctor B B C (idFunctor B) (catEquivForward B C eBC))
              (postWhiskerNatIso B B C
                (compFunctor B A B (catEquivBackward A B eAB) (catEquivForward A B eAB))
                (idFunctor B) (catEquivForward B C eBC)
                (catEquivCounit A B eAB)))
            (compNatIso C C
              (compFunctor C B C (catEquivBackward B C eBC)
                (compFunctor B B C (idFunctor B) (catEquivForward B C eBC)))
              (compFunctor C B C (catEquivBackward B C eBC) (catEquivForward B C eBC))
              (idFunctor C)
              (preWhiskerNatIso C B C (catEquivBackward B C eBC)
                (compFunctor B B C (idFunctor B) (catEquivForward B C eBC))
                (catEquivForward B C eBC)
                (leftUnitor B C (catEquivForward B C eBC)))
              (catEquivCounit B C eBC))))
  /-- Transitivity of category equivalence, packaged from the composed forward/backward functors
  and the derived unit/counit comparisons.  Book target: §1.1.3 after Definition 1.1.9. -/
  lf_def catEquivTrans : (A : SCat) ⇒ (B : SCat) ⇒ (C : SCat) ⇒
      CatEquiv A B ⇒ CatEquiv B C ⇒ CatEquiv A C :=
    fun A B C eAB eBC =>
      catEquivOfData A C
        (compFunctor A B C (catEquivForward A B eAB) (catEquivForward B C eBC))
        (compFunctor C B A (catEquivBackward B C eBC) (catEquivBackward A B eAB))
        (catEquivTransUnit A B C eAB eBC)
        (catEquivTransCounit A B C eAB eBC)
  /-- A section of a functor; Definition 1.1.12.  The displayed natural isomorphism is the data. -/
  syntax_abbrev SectionWitness {C : SCat} {D : SCat} (F : Functor C D) (S : Functor D C)
    (σ : NatIso D D (compFunctor D C D S F) (idFunctor D)) :=
    NatIso D D (compFunctor D C D S F) (idFunctor D)
  /-- A retraction of a functor; Definition 1.1.12.  The displayed natural isomorphism is the data.
  -/
  syntax_abbrev RetractionWitness {C : SCat} {D : SCat} (F : Functor C D) (R : Functor D C)
    (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) :=
    NatIso C C (compFunctor C D C F R) (idFunctor C)
  /-- Retraction data for a category as a retract of another; Definition 1.1.18. -/
  syntax_abbrev RetractWitness {C : SCat} {D : SCat}
    (i : Functor C D) (r : Functor D C)
    (ρ : NatIso C C (compFunctor C D C i r) (idFunctor C)) :=
    NatIso C C (compFunctor C D C i r) (idFunctor C)
  /-- Comparison between the displayed retraction and section inverses in Lemma 1.1.13. -/
  lf_def sectionRetractionBackwardNatIso :
      (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (S : Functor D C) ⇒
      (σ : NatIso D D (compFunctor D C D S F) (idFunctor D)) ⇒
      (R : Functor D C) ⇒
      (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) ⇒
      SectionWitness C D F S σ ⇒ RetractionWitness C D F R ρ ⇒ NatIso D C R S :=
    fun C D F S σ R ρ sec ret =>
      compNatIso D C R (compFunctor D D C (idFunctor D) R) S
        (invNatIso D C (compFunctor D D C (idFunctor D) R) R (leftUnitor D C R))
        (compNatIso D C
          (compFunctor D D C (idFunctor D) R)
          (compFunctor D D C (compFunctor D C D S F) R)
          S
          (postWhiskerNatIso D D C (idFunctor D) (compFunctor D C D S F) R
            (invNatIso D D (compFunctor D C D S F) (idFunctor D) sec))
          (compNatIso D C
            (compFunctor D D C (compFunctor D C D S F) R)
            (compFunctor D C C S (compFunctor C D C F R))
            S
            (assocFunctor D C D C S F R)
            (compNatIso D C
              (compFunctor D C C S (compFunctor C D C F R))
              (compFunctor D C C S (idFunctor C))
              S
              (preWhiskerNatIso D C C S
                (compFunctor C D C F R) (idFunctor C) ret)
              (rightUnitor D C S))))
  /-- Counit comparison used to package a section/retraction pair as an equivalence. -/
  lf_def sectionRetractionCounit :
      (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (S : Functor D C) ⇒
      (σ : NatIso D D (compFunctor D C D S F) (idFunctor D)) ⇒
      (R : Functor D C) ⇒
      (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) ⇒
      SectionWitness C D F S σ ⇒ RetractionWitness C D F R ρ ⇒
      NatIso D D (compFunctor D C D R F) (idFunctor D) :=
    fun C D F S σ R ρ sec ret =>
      compNatIso D D (compFunctor D C D R F) (compFunctor D C D S F) (idFunctor D)
        (postWhiskerNatIso D C D R S F
          (sectionRetractionBackwardNatIso C D F S σ R ρ sec ret))
        sec
  /-- Equivalence from a section and retraction; Lemma 1.1.13. -/
  lf_def catEquivOfSectionRetraction :
      (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (S : Functor D C) ⇒
      (σ : NatIso D D (compFunctor D C D S F) (idFunctor D)) ⇒
      (R : Functor D C) ⇒
      (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) ⇒
      SectionWitness C D F S σ ⇒ RetractionWitness C D F R ρ ⇒ CatEquiv C D :=
    fun C D F S σ R ρ sec ret =>
      catEquivOfData C D F R ret
        (sectionRetractionCounit C D F S σ R ρ sec ret)

  /-- The terminal anima `*`; Axiom B.1. -/
  lf_opaque terminalAnima : Anima
  /-- The terminal category as the underlying category of the terminal anima; Axiom B.1. -/
  lf_def terminalCat : SCat := animaCat terminalAnima
  /-- Absolute objects of a category; Axiom A.2. -/
  syntax_abbrev Obj (C : SCat) := Functor terminalCat C
