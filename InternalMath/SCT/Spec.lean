/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalLean.Command

/-!
# Book-structured intrinsic Synthetic Category Theory interface

This file is a source-facing `InternalLean` presentation of the primitives, axioms, constructors,
and theorem-shaped declarations needed for Chapters 1--7 of the May 2026 Synthetic Category Theory
book project by Cisinski, Cnossen, Nguyen, and Walde. It uses one theory reopened by
`extend_type_theory` blocks, rather than a single large declaration or a chain of separate theories.

The guiding convention is intrinsic: object sorts contain valid data by construction, so there are
no generic `wf...` judgments. Mathematical properties that are not part of a sort remain explicit
witness sorts or judgments. In particular, anima are primitive and have an underlying synthetic
category; the judgment `isAnimaCat` records that the underlying category is an anima-category.

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
  /-- Natural-isomorphism/coherence data between parallel functors; Axiom A.1. -/
  syntax_sort NatIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D) : Type u
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
  /-- Side condition saying that all fibers of an anima-indexed family are anima.  Book context:
  Chapter 1 of the SCT book.
  -/
  judgment allFibersAnima (Γ : Anima) (C : AnimaIndexedCat Γ)
  judgment_role allFibersAnima : side_judgment
  /-- An anima-indexed sum of anima fibers is an anima; Axiom A.1(3). -/
  rule sigma_anima_indexed_is_anima (Γ : Anima) (C : AnimaIndexedCat Γ) where
    premise h : allFibersAnima Γ C
    conclusion : isAnimaCat (sigmaAnimaIndexed Γ C)

  /-- Identity functor; Axiom A.3. -/
  lf_opaque idFunctor (C : SCat) : Functor C C
  /-- Composition of functors; Axiom A.3. -/
  lf_opaque compFunctor (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C D) (G : Functor D E) : Functor C E
  /-- Identity natural isomorphism; Axioms A.1' and A.2'. -/
  lf_opaque idNatIso (C : SCat) (D : SCat) (F : Functor C D) : NatIso C D F F
  /-- Vertical composition of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque compNatIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D)
    (H : Functor C D) (α : NatIso C D F G) (β : NatIso C D G H) : NatIso C D F H
  /-- Inverse natural isomorphism; Axiom A.1. -/
  lf_opaque invNatIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D)
    (α : NatIso C D F G) : NatIso C D G F
  /-- Left unitor for functor composition; Axiom A.3. -/
  lf_opaque leftUnitor (C : SCat) (D : SCat) (F : Functor C D) :
    NatIso C D (compFunctor C C D (idFunctor C) F) F
  /-- Right unitor for functor composition; Axiom A.3. -/
  lf_opaque rightUnitor (C : SCat) (D : SCat) (F : Functor C D) :
    NatIso C D (compFunctor C D D F (idFunctor D)) F
  /-- Associator for functor composition; Axiom A.3. -/
  lf_opaque assocFunctor (B : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    NatIso B E
      (compFunctor B D E (compFunctor B C D F G) H)
      (compFunctor B C E F (compFunctor C D E G H))
  /-- Inverse associator, derived from the associator; Axiom A.3. -/
  lf_def assocFunctorInv : (B : SCat) ⇒ (C : SCat) ⇒ (D : SCat) ⇒ (E : SCat) ⇒
      (F : Functor B C) ⇒ (G : Functor C D) ⇒ (H : Functor D E) ⇒
        NatIso B E (compFunctor B C E F (compFunctor C D E G H))
          (compFunctor B D E (compFunctor B C D F G) H) :=
    fun B C D E F G H => invNatIso B E
      (compFunctor B D E (compFunctor B C D F G) H)
      (compFunctor B C E F (compFunctor C D E G H))
      (assocFunctor B C D E F G H)
  /-- Pre-whiskering of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque preWhiskerNatIso (B : SCat) (C : SCat) (D : SCat)
    (K : Functor B C) (F : Functor C D) (G : Functor C D)
    (α : NatIso C D F G) :
    NatIso B D (compFunctor B C D K F) (compFunctor B C D K G)
  /-- Post-whiskering of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque postWhiskerNatIso (B : SCat) (C : SCat) (D : SCat)
    (F : Functor B C) (G : Functor B C) (K : Functor C D)
    (α : NatIso B C F G) :
    NatIso B D (compFunctor B C D F K) (compFunctor B C D G K)
  /-- Horizontal composition of natural isomorphisms; Axioms A.1' and A.2'. -/
  lf_opaque horizCompNatIso (B : SCat) (C : SCat) (D : SCat)
    (F : Functor B C) (G : Functor B C) (H : Functor C D) (K : Functor C D)
    (α : NatIso B C F G) (β : NatIso C D H K) :
    NatIso B D (compFunctor B C D F H) (compFunctor B C D G K)
  /-- Packaging of equivalence data; definition after Axiom A.3. -/
  lf_opaque catEquivOfData (C : SCat) (D : SCat) (F : Functor C D) (G : Functor D C)
    (η : NatIso C C (compFunctor C D C F G) (idFunctor C))
    (ε : NatIso D D (compFunctor D C D G F) (idFunctor D)) : CatEquiv C D
  /-- Forward functor of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivForward (C : SCat) (D : SCat) (e : CatEquiv C D) : Functor C D
  /-- Backward functor of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivBackward (C : SCat) (D : SCat) (e : CatEquiv C D) : Functor D C
  /-- Unit natural isomorphism of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivUnit (C : SCat) (D : SCat) (e : CatEquiv C D) :
    NatIso C C
      (compFunctor C D C (catEquivForward C D e) (catEquivBackward C D e))
      (idFunctor C)
  /-- Counit natural isomorphism of an equivalence; definition after Axiom A.3. -/
  lf_opaque catEquivCounit (C : SCat) (D : SCat) (e : CatEquiv C D) :
    NatIso D D
      (compFunctor D C D (catEquivBackward C D e) (catEquivForward C D e))
      (idFunctor D)
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
  syntax_abbrev SectionWitness (C : SCat) (D : SCat) (F : Functor C D) (S : Functor D C)
    (σ : NatIso D D (compFunctor D C D S F) (idFunctor D)) :=
    NatIso D D (compFunctor D C D S F) (idFunctor D)
  /-- A retraction of a functor; Definition 1.1.12.  The displayed natural isomorphism is the data.
  -/
  syntax_abbrev RetractionWitness (C : SCat) (D : SCat) (F : Functor C D) (R : Functor D C)
    (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) :=
    NatIso C C (compFunctor C D C F R) (idFunctor C)
  /-- Retraction data for a category as a retract of another; Definition 1.1.18. -/
  syntax_abbrev RetractWitness (C : SCat) (D : SCat)
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

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Isomorphisms between absolute objects.  Book context: Chapter 1 of the SCT book. -/
  syntax_abbrev ObjIso (C : SCat) (x : Obj C) (y : Obj C) := NatIso terminalCat C x y
  /-- Pairing constructor for terms of an anima-indexed dependent sum.  Book context: Chapter 1 of
  the SCT book.
  -/
  lf_opaque sigmaAnimaIndexedPair (Γ : Anima) (C : AnimaIndexedCat Γ)
    (x : Obj (animaCat Γ)) (c : Obj (animaIndexedFiber Γ C x)) :
    Obj (sigmaAnimaIndexed Γ C)
  /-- Fiberwise anima evidence unpacked from the side condition `allFibersAnima`.
  Book target: Axiom A.1(3), closure of anima-indexed sums of anima fibers.
  Status: remaining T-shaped model-facing rule.  To make this book-faithful, make
  `allFibersAnima` expose enough data that this rule is a checked internal theorem rather than a
  model obligation. -/
  rule all_fibers_anima_fiber (Γ : Anima) (C : AnimaIndexedCat Γ)
    (x : Obj (animaCat Γ)) where
    premise h : allFibersAnima Γ C
    conclusion : isAnimaCat (animaIndexedFiber Γ C x)
  /-- General terms of `C` in context `Γ`; Axiom A.2. -/
  syntax_abbrev Term (Γ : SCat) (C : SCat) := Functor Γ C
  /-- The universal term of `C`; Definition 1.1.2. -/
  lf_def universalTerm : (C : SCat) ⇒ Term C C := fun C => idFunctor C
  /-- Compatibility map from object notation to terminal-functor notation; Axiom A.2. -/
  lf_def objectFunctor : (C : SCat) ⇒ Obj C ⇒ Functor terminalCat C :=
    fun C x => x
  /-- Compatibility map from terminal-functor notation to object notation; Axiom A.2. -/
  lf_def objectOfFunctor : (C : SCat) ⇒ Functor terminalCat C ⇒ Obj C :=
    fun C F => F
  /-- Definitional comparison for object/terminal-functor notation; Axiom A.2. -/
  lf_def objectFunctorCounit : (C : SCat) ⇒ (F : Functor terminalCat C) ⇒
      NatIso terminalCat C (objectFunctor C (objectOfFunctor C F)) F :=
    fun C F => idNatIso terminalCat C F

  /-- Terminal projection; Axiom B.1. -/
  lf_opaque terminalProjection (C : SCat) : Functor C terminalCat
  /-- Contractibility of maps into the terminal category; Axiom B.1. -/
  lf_opaque terminalUnique (C : SCat) (F : Functor C terminalCat)
    (G : Functor C terminalCat) : NatIso C terminalCat F G
  /-- Constant functor with value an absolute object.  Book context: Chapter 1 of the SCT book. -/
  lf_def constantFunctor : (C : SCat) ⇒ (D : SCat) ⇒ Obj D ⇒ Functor C D :=
    fun C D x => compFunctor C terminalCat D (terminalProjection C) x
  /-- Contractible category witness, expressed as equivalence to `*`.
  Book context:Chapter 1 of the
  SCT book.
  -/
  syntax_abbrev ContractibleCat (C : SCat) := CatEquiv C terminalCat
  /-- A contraction of `C` onto an object `x`.  Book context: Chapter 1 of the SCT book. -/
  syntax_abbrev ContractionAt (C : SCat) (x : Obj C) :=
    NatIso C C (constantFunctor C C x) (idFunctor C)

  /-- Initial category; Axiom B.2. -/
  lf_opaque initialCat : SCat
  /-- Initial map into any synthetic category; Axiom B.2. -/
  lf_opaque initialElim (C : SCat) : Functor initialCat C
  /-- Contractibility of maps out of the initial category; Axiom B.2. -/
  lf_opaque initialUnique (C : SCat) (F : Functor initialCat C)
    (G : Functor initialCat C) : NatIso initialCat C F G
  /-- Strictness of the initial category; Axiom B.2'. -/
  lf_opaque initialStrict (C : SCat) (F : Functor C initialCat) : CatEquiv C initialCat

  /-- Binary product of synthetic categories; Axiom B.3. -/
  lf_opaque prodCat (C : SCat) (D : SCat) : SCat
  /-- First product projection; Axiom B.3. -/
  lf_opaque prodPr1 (C : SCat) (D : SCat) : Functor (prodCat C D) C
  /-- Second product projection; Axiom B.3. -/
  lf_opaque prodPr2 (C : SCat) (D : SCat) : Functor (prodCat C D) D
  /-- Product pairing; Axiom B.3. -/
  lf_opaque prodPair (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ C) (G : Functor Γ D) : Functor Γ (prodCat C D)
  /-- First product β isomorphism; Axiom B.3. -/
  lf_opaque prodBeta1 (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ C) (G : Functor Γ D) :
    NatIso Γ C (compFunctor Γ (prodCat C D) C (prodPair Γ C D F G) (prodPr1 C D)) F
  /-- Second product β isomorphism; Axiom B.3. -/
  lf_opaque prodBeta2 (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ C) (G : Functor Γ D) :
    NatIso Γ D (compFunctor Γ (prodCat C D) D (prodPair Γ C D F G) (prodPr2 C D)) G
  /-- Product η isomorphism; Axiom B.3. -/
  lf_opaque prodEta (Γ : SCat) (C : SCat) (D : SCat)
    (H : Functor Γ (prodCat C D)) :
    NatIso Γ (prodCat C D)
      (prodPair Γ C D
        (compFunctor Γ (prodCat C D) C H (prodPr1 C D))
        (compFunctor Γ (prodCat C D) D H (prodPr2 C D)))
      H
  /-- Product natural isomorphisms are specified componentwise; Axiom B.3. -/
  lf_opaque prodUniq (Γ : SCat) (C : SCat) (D : SCat)
    (H : Functor Γ (prodCat C D)) (K : Functor Γ (prodCat C D))
    (α : NatIso Γ C
      (compFunctor Γ (prodCat C D) C H (prodPr1 C D))
      (compFunctor Γ (prodCat C D) C K (prodPr1 C D)))
    (β : NatIso Γ D
      (compFunctor Γ (prodCat C D) D H (prodPr2 C D))
      (compFunctor Γ (prodCat C D) D K (prodPr2 C D))) :
    NatIso Γ (prodCat C D) H K

  /-- Binary coproduct of synthetic categories; Axiom B.4. -/
  lf_opaque coprodCat (C : SCat) (D : SCat) : SCat
  /-- First coproduct injection; Axiom B.4. -/
  lf_opaque coprodIn1 (C : SCat) (D : SCat) : Functor C (coprodCat C D)
  /-- Second coproduct injection; Axiom B.4. -/
  lf_opaque coprodIn2 (C : SCat) (D : SCat) : Functor D (coprodCat C D)
  /-- Coproduct case analysis; Axiom B.4. -/
  lf_opaque coprodCase (C : SCat) (D : SCat) (Γ : SCat)
    (F : Functor C Γ) (G : Functor D Γ) : Functor (coprodCat C D) Γ
  /-- First coproduct β isomorphism; Axiom B.4. -/
  lf_opaque coprodBeta1 (C : SCat) (D : SCat) (Γ : SCat)
    (F : Functor C Γ) (G : Functor D Γ) :
    NatIso C Γ
      (compFunctor C (coprodCat C D) Γ (coprodIn1 C D)
        (coprodCase C D Γ F G))
      F
  /-- Second coproduct β isomorphism; Axiom B.4. -/
  lf_opaque coprodBeta2 (C : SCat) (D : SCat) (Γ : SCat)
    (F : Functor C Γ) (G : Functor D Γ) :
    NatIso D Γ
      (compFunctor D (coprodCat C D) Γ (coprodIn2 C D)
        (coprodCase C D Γ F G))
      G
  /-- Coproduct η isomorphism; Axiom B.4. -/
  lf_opaque coprodEta (C : SCat) (D : SCat) (Γ : SCat)
    (H : Functor (coprodCat C D) Γ) :
    NatIso (coprodCat C D) Γ
      (coprodCase C D Γ
        (compFunctor C (coprodCat C D) Γ (coprodIn1 C D) H)
        (compFunctor D (coprodCat C D) Γ (coprodIn2 C D) H))
      H
  /-- Coproduct natural isomorphisms are specified componentwise; Axiom B.4. -/
  lf_opaque coprodUniq (C : SCat) (D : SCat) (Γ : SCat)
    (H : Functor (coprodCat C D) Γ) (K : Functor (coprodCat C D) Γ)
    (α : NatIso C Γ
      (compFunctor C (coprodCat C D) Γ (coprodIn1 C D) H)
      (compFunctor C (coprodCat C D) Γ (coprodIn1 C D) K))
    (β : NatIso D Γ
      (compFunctor D (coprodCat C D) Γ (coprodIn2 C D) H)
      (compFunctor D (coprodCat C D) Γ (coprodIn2 C D) K)) :
    NatIso (coprodCat C D) Γ H K

  /-- Pullback of functors; Axiom B.5. -/
  lf_opaque pullbackCat (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) : SCat
  /-- First pullback projection; Axiom B.5. -/
  lf_opaque pullbackPr1 (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) : Functor (pullbackCat C D E F G) C
  /-- Second pullback projection; Axiom B.5. -/
  lf_opaque pullbackPr2 (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) : Functor (pullbackCat C D E F G) D
  /-- Pullback commutativity isomorphism; Axiom B.5. -/
  lf_opaque pullbackComm (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) :
    NatIso (pullbackCat C D E F G) E
      (compFunctor (pullbackCat C D E F G) C E (pullbackPr1 C D E F G) F)
      (compFunctor (pullbackCat C D E F G) D E (pullbackPr2 C D E F G) G)
  /-- Mediating functor into a pullback from compatible cone data; Axiom B.5. -/
  lf_opaque pullbackLift (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (A : Functor X C) (B : Functor X D)
    (θ : NatIso X E (compFunctor X C E A F) (compFunctor X D E B G)) :
    Functor X (pullbackCat C D E F G)
  /-- First pullback β isomorphism; Axiom B.5. -/
  lf_opaque pullbackBeta1 (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (A : Functor X C) (B : Functor X D)
    (θ : NatIso X E (compFunctor X C E A F) (compFunctor X D E B G)) :
    NatIso X C
      (compFunctor X (pullbackCat C D E F G) C
        (pullbackLift X C D E F G A B θ) (pullbackPr1 C D E F G))
      A
  /-- Second pullback β isomorphism; Axiom B.5. -/
  lf_opaque pullbackBeta2 (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (A : Functor X C) (B : Functor X D)
    (θ : NatIso X E (compFunctor X C E A F) (compFunctor X D E B G)) :
    NatIso X D
      (compFunctor X (pullbackCat C D E F G) D
        (pullbackLift X C D E F G A B θ) (pullbackPr2 C D E F G))
      B
  /-- Pullback natural isomorphisms are specified componentwise; Axiom B.5. -/
  lf_opaque pullbackUniq (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (H : Functor X (pullbackCat C D E F G))
    (K : Functor X (pullbackCat C D E F G))
    (α : NatIso X C
      (compFunctor X (pullbackCat C D E F G) C H (pullbackPr1 C D E F G))
      (compFunctor X (pullbackCat C D E F G) C K (pullbackPr1 C D E F G)))
    (β : NatIso X D
      (compFunctor X (pullbackCat C D E F G) D H (pullbackPr2 C D E F G))
      (compFunctor X (pullbackCat C D E F G) D K (pullbackPr2 C D E F G))) :
    NatIso X (pullbackCat C D E F G) H K
  /-- Pullback η comparison from the projections of a cone; Axiom B.5. -/
  lf_opaque pullbackEta (X : SCat) (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (H : Functor X (pullbackCat C D E F G))
    (θ : NatIso X E
      (compFunctor X C E
        (compFunctor X (pullbackCat C D E F G) C H (pullbackPr1 C D E F G)) F)
      (compFunctor X D E
        (compFunctor X (pullbackCat C D E F G) D H (pullbackPr2 C D E F G)) G)) :
    NatIso X (pullbackCat C D E F G)
      (pullbackLift X C D E F G
        (compFunctor X (pullbackCat C D E F G) C H (pullbackPr1 C D E F G))
        (compFunctor X (pullbackCat C D E F G) D H (pullbackPr2 C D E F G)) θ)
      H
  /-- Fiber of a functor over an absolute object, defined as a pullback.  Book context: Chapter 1 of
  the SCT book.
  -/
  lf_def fiberCat : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒ Obj D ⇒ SCat :=
    fun C D F y => pullbackCat C terminalCat D F y
  /-- Projection from a fiber to the domain.  Book context: Chapter 1 of the SCT book. -/
  lf_def fiberProjection : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (y : Obj D) ⇒ Functor (fiberCat C D F y) C :=
    fun C D F y => pullbackPr1 C terminalCat D F y
  /-- A source-shaped pullback-square predicate for theorem statements, represented by the
  comparison to the pullback object.  Book context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev PullbackSquare (A : SCat) (B : SCat) (C : SCat) (D : SCat)
    (top : Functor A B) (left : Functor A C) (right : Functor B D) (bottom : Functor C D) :=
    CatEquiv A (pullbackCat B C D right bottom)
  /-- Commutative pushout-square witness, represented by the displayed square data.
  Book target: pushout squares used throughout Chapter 1, especially Proposition 1.3.3
  and Axiom J.1.
  Status: remaining T-shaped model-facing sort.  To make this book-faithful, replace this
  witness sort by a source-shaped universal property or a checked abbreviation from explicit
  pushout data. -/
  syntax_sort PushoutSquare (A : SCat) (B : SCat) (C : SCat) (D : SCat)
    (top : Functor A B) (left : Functor A C) (right : Functor B D) (bottom : Functor C D) : Type u
  /-- Embedding evidence for a functor, represented by equivalence with the self-pullback.  Book
  context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev Embedding (C : SCat) (D : SCat) (F : Functor C D) :=
    CatEquiv C (pullbackCat C C D F F)

  -- B.4' coproduct universality is stated after pullbacks for dependency order.
  /-- Base-change decomposition category for coproducts; Axiom B.4'. -/
  lf_def coprodBaseChangeCat : (C : SCat) ⇒ (D : SCat) ⇒ (X : SCat) ⇒
      (f : Functor X (coprodCat C D)) ⇒ SCat :=
    fun C D X f => coprodCat
      (pullbackCat X C (coprodCat C D) f (coprodIn1 C D))
      (pullbackCat X D (coprodCat C D) f (coprodIn2 C D))
  /-- Forward comparison for coproduct base change; Axiom B.4'. -/
  lf_opaque coprodBaseChangeForward (C : SCat) (D : SCat) (X : SCat)
    (f : Functor X (coprodCat C D)) : Functor (coprodBaseChangeCat C D X f) X
  /-- Backward comparison for coproduct base change; Axiom B.4'. -/
  lf_opaque coprodBaseChangeBackward (C : SCat) (D : SCat) (X : SCat)
    (f : Functor X (coprodCat C D)) : Functor X (coprodBaseChangeCat C D X f)
  /-- Unit for coproduct base change; Axiom B.4'. -/
  lf_opaque coprodBaseChangeUnit (C : SCat) (D : SCat) (X : SCat)
    (f : Functor X (coprodCat C D)) :
    NatIso (coprodBaseChangeCat C D X f) (coprodBaseChangeCat C D X f)
      (compFunctor (coprodBaseChangeCat C D X f) X (coprodBaseChangeCat C D X f)
        (coprodBaseChangeForward C D X f) (coprodBaseChangeBackward C D X f))
      (idFunctor (coprodBaseChangeCat C D X f))
  /-- Counit for coproduct base change; Axiom B.4'. -/
  lf_opaque coprodBaseChangeCounit (C : SCat) (D : SCat) (X : SCat)
    (f : Functor X (coprodCat C D)) :
    NatIso X X
      (compFunctor X (coprodBaseChangeCat C D X f) X
        (coprodBaseChangeBackward C D X f) (coprodBaseChangeForward C D X f))
      (idFunctor X)
  /-- Coproduct base-change equivalence; Axiom B.4'. -/
  lf_def coprodBaseChangeEquiv : (C : SCat) ⇒ (D : SCat) ⇒ (X : SCat) ⇒
      (f : Functor X (coprodCat C D)) ⇒ CatEquiv (coprodBaseChangeCat C D X f) X :=
    fun C D X f => catEquivOfData (coprodBaseChangeCat C D X f) X
      (coprodBaseChangeForward C D X f) (coprodBaseChangeBackward C D X f)
      (coprodBaseChangeUnit C D X f) (coprodBaseChangeCounit C D X f)

  /-- Pullback expressing coproduct disjointness; Axiom B.4'. -/
  lf_def coprodDisjointPullback : (C : SCat) ⇒ (D : SCat) ⇒ SCat :=
    fun C D => pullbackCat C D (coprodCat C D) (coprodIn1 C D) (coprodIn2 C D)
  /-- Forward comparison for coproduct disjointness; Axiom B.4'. -/
  lf_opaque coprodDisjointForward (C : SCat) (D : SCat) :
    Functor (coprodDisjointPullback C D) initialCat
  /-- Backward comparison for coproduct disjointness; Axiom B.4'. -/
  lf_opaque coprodDisjointBackward (C : SCat) (D : SCat) :
    Functor initialCat (coprodDisjointPullback C D)
  /-- Unit for coproduct disjointness; Axiom B.4'. -/
  lf_opaque coprodDisjointUnit (C : SCat) (D : SCat) :
    NatIso (coprodDisjointPullback C D) (coprodDisjointPullback C D)
      (compFunctor (coprodDisjointPullback C D) initialCat
        (coprodDisjointPullback C D) (coprodDisjointForward C D)
        (coprodDisjointBackward C D))
      (idFunctor (coprodDisjointPullback C D))
  /-- Counit for coproduct disjointness; Axiom B.4'. -/
  lf_opaque coprodDisjointCounit (C : SCat) (D : SCat) :
    NatIso initialCat initialCat
      (compFunctor initialCat (coprodDisjointPullback C D) initialCat
        (coprodDisjointBackward C D) (coprodDisjointForward C D))
      (idFunctor initialCat)
  /-- Coproducts are disjoint; Axiom B.4'. -/
  lf_def coprodDisjoint : (C : SCat) ⇒ (D : SCat) ⇒
      CatEquiv (coprodDisjointPullback C D) initialCat :=
    fun C D => catEquivOfData (coprodDisjointPullback C D) initialCat
      (coprodDisjointForward C D) (coprodDisjointBackward C D)
      (coprodDisjointUnit C D) (coprodDisjointCounit C D)

  /-- Functor category; Axiom B.6. -/
  lf_opaque funCat (C : SCat) (D : SCat) : SCat
  /-- Precomposition functor between functor categories; Axiom B.6. -/
  lf_opaque precompFunctor (A : SCat) (B : SCat) (C : SCat) (u : Functor A B) :
    Functor (funCat B C) (funCat A C)
  /-- Mapping-out universal property associated to a pushout-square witness.  InternalLean cannot
  yet use this Pi-shaped type directly as an opaque witness result, so the universal property is a
  projection from the witness sort. -/
  lf_opaque pushoutSquareMappingEquiv (A : SCat) (B : SCat) (C : SCat) (D : SCat)
    (top : Functor A B) (left : Functor A C) (right : Functor B D) (bottom : Functor C D)
    (sq : PushoutSquare A B C D top left right bottom) (X : SCat) :
    CatEquiv (funCat D X)
      (pullbackCat (funCat B X) (funCat C X) (funCat A X)
        (precompFunctor A B X top) (precompFunctor A C X left))
  /-- Postcomposition functor between functor categories; Axiom B.6. -/
  lf_opaque postcompFunctor (A : SCat) (B : SCat) (C : SCat) (v : Functor B C) :
    Functor (funCat A B) (funCat A C)
  /-- Evaluation functor; Axiom B.6. -/
  lf_opaque evalFunctor (C : SCat) (D : SCat) : Functor (prodCat (funCat C D) C) D
  /-- Currying; Axiom B.6. -/
  lf_opaque curryFunctor (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor (prodCat Γ C) D) : Functor Γ (funCat C D)
  /-- Uncurrying; Axiom B.6. -/
  lf_opaque uncurryFunctor (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ (funCat C D)) : Functor (prodCat Γ C) D
  /-- β isomorphism for curry/uncurry; Axiom B.6. -/
  lf_opaque curryBeta (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor (prodCat Γ C) D) :
    NatIso (prodCat Γ C) D (uncurryFunctor Γ C D (curryFunctor Γ C D F)) F
  /-- η isomorphism for curry/uncurry; Axiom B.6. -/
  lf_opaque curryEta (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ (funCat C D)) :
    NatIso Γ (funCat C D) (curryFunctor Γ C D (uncurryFunctor Γ C D F)) F
  /-- Currying of natural isomorphisms; Axiom B.6. -/
  lf_opaque curryNatIso (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor (prodCat Γ C) D) (G : Functor (prodCat Γ C) D)
    (α : NatIso (prodCat Γ C) D F G) :
    NatIso Γ (funCat C D) (curryFunctor Γ C D F) (curryFunctor Γ C D G)
  /-- Uncurrying of natural isomorphisms; Axiom B.6. -/
  lf_opaque uncurryNatIso (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ (funCat C D)) (G : Functor Γ (funCat C D))
    (α : NatIso Γ (funCat C D) F G) :
    NatIso (prodCat Γ C) D (uncurryFunctor Γ C D F) (uncurryFunctor Γ C D G)
  /-- Forward functor of the currying equivalence; Axiom B.6. -/
  lf_opaque curryUncurryForward (Γ : SCat) (C : SCat) (D : SCat) :
    Functor (funCat Γ (funCat C D)) (funCat (prodCat Γ C) D)
  /-- Backward functor of the currying equivalence; Axiom B.6. -/
  lf_opaque curryUncurryBackward (Γ : SCat) (C : SCat) (D : SCat) :
    Functor (funCat (prodCat Γ C) D) (funCat Γ (funCat C D))
  /-- Unit of the currying equivalence; Axiom B.6. -/
  lf_opaque curryUncurryUnit (Γ : SCat) (C : SCat) (D : SCat) :
    NatIso (funCat Γ (funCat C D)) (funCat Γ (funCat C D))
      (compFunctor (funCat Γ (funCat C D))
        (funCat (prodCat Γ C) D) (funCat Γ (funCat C D))
        (curryUncurryForward Γ C D) (curryUncurryBackward Γ C D))
      (idFunctor (funCat Γ (funCat C D)))
  /-- Counit of the currying equivalence; Axiom B.6. -/
  lf_opaque curryUncurryCounit (Γ : SCat) (C : SCat) (D : SCat) :
    NatIso (funCat (prodCat Γ C) D) (funCat (prodCat Γ C) D)
      (compFunctor (funCat (prodCat Γ C) D)
        (funCat Γ (funCat C D)) (funCat (prodCat Γ C) D)
        (curryUncurryBackward Γ C D) (curryUncurryForward Γ C D))
      (idFunctor (funCat (prodCat Γ C) D))
  /-- Packaged currying equivalence; Axiom B.6. -/
  lf_def curryUncurryEquiv : (Γ : SCat) ⇒ (C : SCat) ⇒ (D : SCat) ⇒
      CatEquiv (funCat Γ (funCat C D)) (funCat (prodCat Γ C) D) :=
    fun Γ C D => catEquivOfData (funCat Γ (funCat C D)) (funCat (prodCat Γ C) D)
      (curryUncurryForward Γ C D) (curryUncurryBackward Γ C D)
      (curryUncurryUnit Γ C D) (curryUncurryCounit Γ C D)
  /-- The walking interval `[1]`; Axiom C.1. -/
  lf_opaque intervalCat : SCat
  /-- The initial endpoint `0 : [1]`; Axiom C.2. -/
  lf_opaque intervalZero : Obj intervalCat
  /-- The terminal endpoint `1 : [1]`; Axiom C.2. -/
  lf_opaque intervalOne : Obj intervalCat
  /-- The source endpoint as a functor `* → [1]`; Axiom C.1. -/
  lf_def intervalZeroFunctor : Functor terminalCat intervalCat := intervalZero
  /-- The target endpoint as a functor `* → [1]`; Axiom C.1. -/
  lf_def intervalOneFunctor : Functor terminalCat intervalCat := intervalOne
  /-- The walking arrow, viewed as an object of `Fun([1],[1])`; Axiom C.1. -/
  lf_def intervalArrow : Functor intervalCat intervalCat := idFunctor intervalCat
  /-- `[0]` is the terminal category; Axiom C.1 and Axiom B.1. -/
  lf_def simplex0Cat : SCat := terminalCat
  /-- `[2]` is defined as `Fun([1],[1])` in this skeleton; Axiom C. -/
  lf_def simplex2Cat : SCat := funCat intervalCat intervalCat
  /-- The identity-at-0 object of `[2]`; Axiom C. -/
  lf_opaque simplex2Id0 : Obj simplex2Cat
  /-- The canonical-arrow object of `[2]`; Axiom C. -/
  lf_opaque simplex2Can : Obj simplex2Cat
  /-- The identity-at-1 object of `[2]`; Axiom C. -/
  lf_opaque simplex2Id1 : Obj simplex2Cat
  /-- First edge face map `[1] → [2]`; Axiom C. -/
  lf_opaque simplex2Face01 : Functor intervalCat simplex2Cat
  /-- Second edge face map `[1] → [2]`; Axiom C. -/
  lf_opaque simplex2Face12 : Functor intervalCat simplex2Cat
  /-- Long-edge face map `[1] → [2]`; Axiom C. -/
  lf_opaque simplex2Face02 : Functor intervalCat simplex2Cat
  /-- Face `d₀ = max : [1] → [2]`; Convention 1.6.13.  Book context: Chapter 1 of the SCT book. -/
  lf_def simplex2FaceD0 : Functor intervalCat simplex2Cat := simplex2Face12
  /-- Face `d₁ = p_[1]^* : [1] → [2]`; Convention 1.6.13.  Book context: Chapter 1 of the SCT book.
  -/
  lf_def simplex2FaceD1 : Functor intervalCat simplex2Cat := simplex2Face02
  /-- Face `d₂ = min : [1] → [2]`; Convention 1.6.13.  Book context: Chapter 1 of the SCT book. -/
  lf_def simplex2FaceD2 : Functor intervalCat simplex2Cat := simplex2Face01
  /-- Endpoint face `d₁ : [0] → [1]`, selecting endpoint `0`.  Book context: Chapter 1 of the SCT
  book.
  -/
  lf_def intervalEndpointD1 : Functor simplex0Cat intervalCat := intervalZero
  /-- Endpoint face `d₀ : [0] → [1]`, selecting endpoint `1`.  Book context: Chapter 1 of the SCT
  book.
  -/
  lf_def intervalEndpointD0 : Functor simplex0Cat intervalCat := intervalOne
  /-- Source degeneracy `[0] → [2]`; Axiom C. -/
  lf_opaque simplex2Deg0 : Functor simplex0Cat simplex2Cat
  /-- Target degeneracy `[0] → [2]`; Axiom C. -/
  lf_opaque simplex2Deg1 : Functor simplex0Cat simplex2Cat
  /-- The first face starts at `id₀`; Axiom C. -/
  lf_opaque simplex2Face01Zero :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalZero simplex2Face01)
      simplex2Id0
  /-- The first face ends at `can`; Axiom C. -/
  lf_opaque simplex2Face01One :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalOne simplex2Face01)
      simplex2Can
  /-- The second face starts at `can`; Axiom C. -/
  lf_opaque simplex2Face12Zero :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalZero simplex2Face12)
      simplex2Can
  /-- The second face ends at `id₁`; Axiom C. -/
  lf_opaque simplex2Face12One :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalOne simplex2Face12)
      simplex2Id1
  /-- The long face starts at `id₀`; Axiom C. -/
  lf_opaque simplex2Face02Zero :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalZero simplex2Face02)
      simplex2Id0
  /-- The long face ends at `id₁`; Axiom C. -/
  lf_opaque simplex2Face02One :
    NatIso terminalCat simplex2Cat
      (compFunctor terminalCat intervalCat simplex2Cat intervalOne simplex2Face02)
      simplex2Id1
  /-- Source degeneracy selects `id₀`; Axiom C. -/
  lf_opaque simplex2Deg0Beta : NatIso simplex0Cat simplex2Cat simplex2Deg0 simplex2Id0
  /-- Target degeneracy selects `id₁`; Axiom C. -/
  lf_opaque simplex2Deg1Beta : NatIso simplex0Cat simplex2Cat simplex2Deg1 simplex2Id1
  /-- The walking square `[1] × [1]`; Axiom D. -/
  lf_def squareCat : SCat := prodCat intervalCat intervalCat

  /-- Evaluation identifies `Fun(*, C)` with `C` on the nose for endpoint projections used here.
  Book context: Chapter 1 of the SCT book.
  -/
  lf_def functorCategoryTerminalEval : (C : SCat) ⇒ Functor (funCat terminalCat C) C :=
    fun C => compFunctor (funCat terminalCat C)
      (prodCat (funCat terminalCat C) terminalCat) C
      (prodPair (funCat terminalCat C) (funCat terminalCat C) terminalCat
        (idFunctor (funCat terminalCat C)) (terminalProjection (funCat terminalCat C)))
      (evalFunctor terminalCat C)
  /-- Source of a morphism in `C`; Axiom C.1. -/
  lf_def sourceFunctor : (C : SCat) ⇒ Functor (funCat intervalCat C) C :=
    fun C => compFunctor (funCat intervalCat C) (funCat terminalCat C) C
      (precompFunctor terminalCat intervalCat C intervalZero) (functorCategoryTerminalEval C)
  /-- Target of a morphism in `C`; Axiom C.1. -/
  lf_def targetFunctor : (C : SCat) ⇒ Functor (funCat intervalCat C) C :=
    fun C => compFunctor (funCat intervalCat C) (funCat terminalCat C) C
      (precompFunctor terminalCat intervalCat C intervalOne) (functorCategoryTerminalEval C)
  /-- Degeneracy `s₀ = ev0 : [2] → [1]`; Convention 1.6.13.
  Book context:Chapter 1 of the SCT book.
  -/
  lf_def simplex2DegS0 : Functor simplex2Cat intervalCat := sourceFunctor intervalCat
  /-- Degeneracy `s₁ = ev1 : [2] → [1]`; Convention 1.6.13.
  Book context:Chapter 1 of the SCT book.
  -/
  lf_def simplex2DegS1 : Functor simplex2Cat intervalCat := targetFunctor intervalCat
  /-- Source object of an interval-shaped morphism; Axiom C.1. -/
  lf_def sourceObj : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒ Obj C :=
    fun C f => compFunctor terminalCat intervalCat C intervalZero f
  /-- Target object of an interval-shaped morphism; Axiom C.1. -/
  lf_def targetObj : (C : SCat) ⇒ (f : Functor intervalCat C) ⇒ Obj C :=
    fun C f => compFunctor terminalCat intervalCat C intervalOne f
  /-- Fiber of the source map over an absolute object.  Book context: Chapter 1 of the SCT book. -/
  lf_def objectSourceFiberCat : (C : SCat) ⇒ Obj C ⇒ SCat :=
    fun C x => pullbackCat (funCat intervalCat C) terminalCat C (sourceFunctor C) x
  /-- Target map from the source fiber over an absolute object.  Book context: Chapter 1 of the SCT
  book.
  -/
  lf_def objectSourceFiberTarget : (C : SCat) ⇒ (x : Obj C) ⇒
      Functor (objectSourceFiberCat C x) C :=
    fun C x => compFunctor (objectSourceFiberCat C x) (funCat intervalCat C) C
      (pullbackPr1 (funCat intervalCat C) terminalCat C (sourceFunctor C) x)
      (targetFunctor C)
  /-- Category of arrows between two absolute objects, as an endpoint fiber.
  Book context:Chapter 1
  of the SCT book.
  -/
  lf_def objectHomCat : (C : SCat) ⇒ Obj C ⇒ Obj C ⇒ SCat :=
    fun C x y => pullbackCat (objectSourceFiberCat C x) terminalCat C
      (objectSourceFiberTarget C x) y
  /-- Initial-object witness for an object of a synthetic category.
  Book target: the initial-object characterization used in §1.2 and later in §5.5. -/
  syntax_abbrev InitialObjectWitness (C : SCat) (x : Obj C) :=
    (y : Obj C) → CatEquiv (objectHomCat C x y) terminalCat
  /-- Terminal-object witness for an object of a synthetic category.
  Book target: the terminal-object characterization used in §1.2 and later in §5.5. -/
  syntax_abbrev TerminalObjectWitness (C : SCat) (x : Obj C) :=
    (y : Obj C) → CatEquiv (objectHomCat C y x) terminalCat
  /-- Outgoing homs from an initial object are contractible, by projecting its witness. -/
  lf_def initialObjectHomContractible :
      (C : SCat) ⇒ (x : Obj C) ⇒ InitialObjectWitness C x ⇒
      (y : Obj C) ⇒ CatEquiv (objectHomCat C x y) terminalCat :=
    fun C x h y => h y
  /-- Incoming homs to a terminal object are contractible, by projecting its witness. -/
  lf_def terminalObjectHomContractible :
      (C : SCat) ⇒ (x : Obj C) ⇒ TerminalObjectWitness C x ⇒
      (y : Obj C) ⇒ CatEquiv (objectHomCat C y x) terminalCat :=
    fun C x h y => h y
  /-- Hom-contractibility data for the source endpoint of `[1]`; Axiom C.2. -/
  lf_opaque intervalZeroInitialHomContractible (y : Obj intervalCat) :
    CatEquiv (objectHomCat intervalCat intervalZero y) terminalCat
  /-- The source endpoint is initial in `[1]`; Axiom C.2. -/
  lf_def intervalZeroInitial : InitialObjectWitness intervalCat intervalZero :=
    fun y => intervalZeroInitialHomContractible y
  /-- Hom-contractibility data for the target endpoint of `[1]`; Axiom C.2. -/
  lf_opaque intervalOneTerminalHomContractible (y : Obj intervalCat) :
    CatEquiv (objectHomCat intervalCat y intervalOne) terminalCat
  /-- The target endpoint is terminal in `[1]`; Axiom C.2. -/
  lf_def intervalOneTerminal : TerminalObjectWitness intervalCat intervalOne :=
    fun y => intervalOneTerminalHomContractible y
  /-- A functor, viewed as an object of the corresponding functor category.  Book context: Chapter 1
  of the SCT book.
  -/
  lf_def functorObject : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒ Obj (funCat C D) :=
    fun C D F => curryFunctor terminalCat C D
      (compFunctor (prodCat terminalCat C) C D (prodPr2 terminalCat C) F)
  /-- The source endpoint of the object classified by an interval-shaped functor.  This is the
  endpoint β-data of the functor-category object notation used by the Segal pullback. -/
  lf_opaque functorObjectSourceCompat (C : SCat) (f : Functor intervalCat C) :
    NatIso terminalCat C
      (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C f)
        (sourceFunctor C))
      (sourceObj C f)
  /-- The target endpoint of the object classified by an interval-shaped functor.  This is the
  endpoint β-data of the functor-category object notation used by the Segal pullback. -/
  lf_opaque functorObjectTargetCompat (C : SCat) (f : Functor intervalCat C) :
    NatIso terminalCat C
      (compFunctor terminalCat (funCat intervalCat C) C (functorObject intervalCat C f)
        (targetFunctor C))
      (targetObj C f)

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
  /-- Natural transformations are objects of the source-shaped natural-transformation category.
  Book context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev NatTrans (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D) :=
    Obj (natTransCat C D F G)

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Regard a natural isomorphism as a natural transformation.
  Book target: Axioms A.1'/A.2', viewing a natural isomorphism as a natural transformation.
  Since `NatIso` is primitive at this stage of the interface, its underlying natural transformation
  is primitive projection data rather than a theorem-shaped admission. -/
  lf_opaque natIsoToNatTrans (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D)
    (α : NatIso C D F G) : NatTrans C D F G

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Higher isomorphisms between natural isomorphisms, represented in the natural-transformation
  fiber.  Book context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev NatIsoIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D)
    (α : NatIso C D F G) (β : NatIso C D F G) :=
    ObjIso (natTransCat C D F G) (natIsoToNatTrans C D F G α) (natIsoToNatTrans C D F G β)
  /-- Underlying arrow in the functor category represented by a natural transformation.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_def natTransUnderlyingArrow : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ NatTrans C D F G ⇒ Functor intervalCat (funCat C D) :=
    fun C D F G α => functorFromObject intervalCat (funCat C D)
      (compFunctor terminalCat (natTransCat C D F G) (funCat intervalCat (funCat C D)) α
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
      (G : Functor C D) ⇒ NatTrans C D F G ⇒ Obj C ⇒ Functor intervalCat D :=
    fun C D F G α x => compFunctor intervalCat (prodCat intervalCat C) D
      (prodPair intervalCat intervalCat C (idFunctor intervalCat) (constantFunctor intervalCat C x))
      (uncurryFunctor intervalCat C D (natTransUnderlyingArrow C D F G α))
  /-- Reflexivity higher isomorphism between natural isomorphisms.  Book context: Chapter 1 of the
  SCT book.
  -/
  lf_def idNatIsoIso : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (G : Functor C D) ⇒ (α : NatIso C D F G) ⇒ NatIsoIso C D F G α α :=
    fun C D F G α => idNatIso terminalCat (natTransCat C D F G)
      (natIsoToNatTrans C D F G α)
  /-- Horizontal composition preserves identity natural isomorphisms; finite A.1'/A.2' coherence.
  Book context: Chapter 1 of the SCT book.
  -/
  lf_opaque horizCompIdId (B : SCat) (C : SCat) (D : SCat)
    (F : Functor B C) (G : Functor C D) :
    NatIsoIso B D (compFunctor B C D F G) (compFunctor B C D F G)
      (horizCompNatIso B C D F F G G (idNatIso B C F) (idNatIso C D G))
      (idNatIso B D (compFunctor B C D F G))
  /-- Horizontal composition preserves vertical composition; finite A.1'/A.2' coherence.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_opaque horizCompCompComp (B : SCat) (C : SCat) (D : SCat)
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
        (horizCompNatIso B C D F₁ F₂ G₁ G₂ α₁ β₁))
  /-- Horizontal composition by an identity on the left is compatible with unitors.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_opaque horizCompLeftId (B : SCat) (C : SCat) (D : SCat)
    (F : Functor B C) (G : Functor B C) (H : Functor C D)
    (α : NatIso B C F G) :
    NatIsoIso B D (compFunctor B C D F H) (compFunctor B C D G H)
      (horizCompNatIso B C D F G H H α (idNatIso C D H))
      (postWhiskerNatIso B C D F G H α)
  /-- Horizontal composition by an identity on the right is compatible with unitors.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_opaque horizCompRightId (B : SCat) (C : SCat) (D : SCat)
    (F : Functor B C) (G : Functor C D) (H : Functor C D)
    (α : NatIso C D G H) :
    NatIsoIso B D (compFunctor B C D F G) (compFunctor B C D F H)
      (horizCompNatIso B C D F F G H (idNatIso B C F) α)
      (preWhiskerNatIso B C D F G H α)
  /-- Associator naturality for whiskered natural isomorphisms; finite A.1'/A.2' coherence.  Book
  context: Chapter 1 of the SCT book.
  -/
  lf_opaque assocFunctorNaturality (A : SCat) (B : SCat) (C : SCat) (D : SCat)
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
          (horizCompNatIso B C D G₀ G₁ H₀ H₁ β γ)))
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

  /-- Lower triangular inclusion `[2] → [1] × [1]`; Axiom D. -/
  lf_opaque squareLowerTriangle : Functor simplex2Cat squareCat
  /-- Upper triangular inclusion `[2] → [1] × [1]`; Axiom D. -/
  lf_opaque squareUpperTriangle : Functor simplex2Cat squareCat
  /-- Boundary category of compatible square restrictions; Axiom D. -/
  lf_def compatibleTriangleCat : SCat ⇒ SCat :=
    fun C => pullbackCat (funCat simplex2Cat C) (funCat simplex2Cat C)
      (funCat intervalCat C)
      (precompFunctor intervalCat simplex2Cat C simplex2FaceD1)
      (precompFunctor intervalCat simplex2Cat C simplex2FaceD1)
  /-- Restriction of a square to compatible triangle data; Axiom D. -/
  lf_opaque squareRestriction (C : SCat) :
    Functor (funCat squareCat C) (compatibleTriangleCat C)
  /-- Chosen extension of compatible triangle data to a square; Axiom D. -/
  lf_opaque squareExtension (C : SCat) :
    Functor (compatibleTriangleCat C) (funCat squareCat C)
  /-- Unit for the square-restriction equivalence; Axiom D. -/
  lf_opaque squareRestrictionUnit (C : SCat) :
    NatIso (funCat squareCat C) (funCat squareCat C)
      (compFunctor (funCat squareCat C) (compatibleTriangleCat C) (funCat squareCat C)
        (squareRestriction C) (squareExtension C))
      (idFunctor (funCat squareCat C))
  /-- Counit for the square-restriction equivalence; Axiom D. -/
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

  /-- Segal restriction from `[2]`-diagrams to composable-pair data; Axiom E. -/
  lf_opaque segalRestriction (C : SCat) :
    Functor (funCat simplex2Cat C) (composableMorphismsCat C)
  /-- Chosen inverse/extension for the Segal restriction; Axiom E. -/
  lf_opaque segalExtension (C : SCat) :
    Functor (composableMorphismsCat C) (funCat simplex2Cat C)
  /-- Unit for the Segal equivalence; Axiom E. -/
  lf_opaque segalUnit (C : SCat) :
    NatIso (funCat simplex2Cat C) (funCat simplex2Cat C)
      (compFunctor (funCat simplex2Cat C) (composableMorphismsCat C)
        (funCat simplex2Cat C) (segalRestriction C) (segalExtension C))
      (idFunctor (funCat simplex2Cat C))
  /-- Counit for the Segal equivalence; Axiom E. -/
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

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Source law for a Segal composite; split Axiom E data for the chosen Segal extension. -/
  lf_opaque compositeSourceCompat (C : SCat)
    (p : Obj (composableMorphismsCat C)) :
    NatIso terminalCat C (sourceObj C (compositeOfComposablePair C p))
      (compFunctor terminalCat (funCat intervalCat C) C
        (compFunctor terminalCat (composableMorphismsCat C) (funCat intervalCat C) p
          (pullbackPr1 (funCat intervalCat C) (funCat intervalCat C) C
            (targetFunctor C) (sourceFunctor C)))
        (sourceFunctor C))
  /-- Target law for a Segal composite; split Axiom E data for the chosen Segal extension. -/
  lf_opaque compositeTargetCompat (C : SCat)
    (p : Obj (composableMorphismsCat C)) :
    NatIso terminalCat C (targetObj C (compositeOfComposablePair C p))
      (compFunctor terminalCat (funCat intervalCat C) C
        (compFunctor terminalCat (composableMorphismsCat C) (funCat intervalCat C) p
          (pullbackPr2 (funCat intervalCat C) (funCat intervalCat C) C
            (targetFunctor C) (sourceFunctor C)))
        (targetFunctor C))

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

  /-- Explicit inverse data for an interval-shaped morphism.  This breaks the previous circular
  definition of invertibility through `Iso(C)`: the category `Iso(C)` should eventually be built
  from this data, while Axiom F still supplies the Rezk equivalence for that category.
  -/
  syntax_sort InvertibleMorphismData (C : SCat) (f : Functor intervalCat C) : Type u
  syntax_sort_role InvertibleMorphismData : side_structure
  /-- Predicate-like witness that an interval-shaped morphism is invertible.  Book target:
  Definition 1.8.2, before packaging invertible morphisms into `Iso(C)`.
  -/
  syntax_abbrev InvertibleMorphism (C : SCat) (f : Functor intervalCat C) :=
    InvertibleMorphismData C f
  /-- Chosen inverse arrow of an invertible interval-shaped morphism. -/
  lf_opaque invertibleMorphismInverse (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) : Functor intervalCat C
  /-- The inverse arrow starts at the target of the original morphism. -/
  lf_opaque invertibleMorphismInverseSource (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso terminalCat C (sourceObj C (invertibleMorphismInverse C f h)) (targetObj C f)
  /-- The inverse arrow ends at the source of the original morphism. -/
  lf_opaque invertibleMorphismInverseTarget (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso terminalCat C (targetObj C (invertibleMorphismInverse C f h)) (sourceObj C f)
  /-- Composing a morphism with its inverse on the right gives the identity at its source. -/
  lf_opaque invertibleMorphismLeftUnit (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso intervalCat C
      (composeComposableMorphism C f (invertibleMorphismInverse C f h)
        (invNatIso terminalCat C (sourceObj C (invertibleMorphismInverse C f h))
          (targetObj C f) (invertibleMorphismInverseSource C f h)))
      (identityMorphism C (sourceObj C f))
  /-- Composing an inverse on the left with the morphism gives the identity at its target. -/
  lf_opaque invertibleMorphismRightUnit (C : SCat) (f : Functor intervalCat C)
    (h : InvertibleMorphism C f) :
    NatIso intervalCat C
      (composeComposableMorphism C (invertibleMorphismInverse C f h) f
        (invertibleMorphismInverseTarget C f h))
      (identityMorphism C (targetObj C f))

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Left unit for the chosen Segal composition; split Axiom E coherence data. -/
  lf_opaque composeLeftUnit (C : SCat) (f : Functor intervalCat C) :
    NatIso intervalCat C
      (composeComposableMorphism C (identityMorphism C (sourceObj C f)) f
        (composeLeftUnitCompat C f))
      f
  /-- Right unit for the chosen Segal composition; split Axiom E coherence data. -/
  lf_opaque composeRightUnit (C : SCat) (f : Functor intervalCat C) :
    NatIso intervalCat C
      (composeComposableMorphism C f (identityMorphism C (targetObj C f))
        (composeRightUnitCompat C f))
      f
  /-- Associativity for Segal composition with explicit endpoint coherences; split Axiom E
  coherence data. -/
  lf_opaque composeAssoc (C : SCat)
    (f : Functor intervalCat C) (g : Functor intervalCat C) (h : Functor intervalCat C)
    (α : NatIso terminalCat C (targetObj C f) (sourceObj C g))
    (β : NatIso terminalCat C (targetObj C g) (sourceObj C h))
    (γL : NatIso terminalCat C
      (targetObj C (composeComposableMorphism C f g α)) (sourceObj C h))
    (γR : NatIso terminalCat C
      (targetObj C f) (sourceObj C (composeComposableMorphism C g h β))) :
    NatIso intervalCat C
      (composeComposableMorphism C (composeComposableMorphism C f g α) h γL)
      (composeComposableMorphism C f (composeComposableMorphism C g h β) γR)

/-- Chapter 2: groupoids, anima, and the groupoid core; Axiom G. -/
extend_type_theory SCT where

  model_section Chapter2


  /-- Witness that a synthetic category is a groupoid; Axiom G. -/
  syntax_sort GroupoidWitness (C : SCat) : Type u
  /-- Every primitive anima has a groupoidal underlying category; Axiom G. -/
  lf_opaque groupoidOfAnima (A : Anima) : GroupoidWitness (animaCat A)
  /-- A groupoid determines an anima; Axiom G. -/
  lf_opaque animaOfGroupoid (C : SCat) (g : GroupoidWitness C) : Anima
  /-- Constant-arrow comparison `C → Fun([1], C)` for groupoids; Axiom G. -/
  lf_opaque groupoidConstArrowFunctor (C : SCat) : Functor C (funCat intervalCat C)
  /-- Groupoid characterization by the interval-arrow comparison; Axiom G. -/
  lf_opaque groupoidIntervalEquiv (C : SCat) (g : GroupoidWitness C) :
    CatEquiv C (funCat intervalCat C)
  /-- The groupoid/anima comparison; Axiom G. -/
  lf_opaque animaOfGroupoidEquiv (C : SCat) (g : GroupoidWitness C) :
    CatEquiv (animaCat (animaOfGroupoid C g)) C
  /-- Reverse groupoid/anima comparison, derived by equivalence symmetry; Axiom G. -/
  lf_def groupoid_anima_equiv :
      (C : SCat) ⇒ (g : GroupoidWitness C) ⇒
        CatEquiv C (animaCat (animaOfGroupoid C g)) :=
    fun C g => catEquivSymm (animaCat (animaOfGroupoid C g)) C
      (animaOfGroupoidEquiv C g)
  /-- The groupoid core of a synthetic category, source-faithfully `Map(*, C)`.  Book context:
  Chapter 2 of the SCT book.
  -/
  lf_def coreAnima : SCat ⇒ Anima := fun C => mapAnima terminalCat C
  /-- Underlying category of the groupoid core; Axiom G. -/
  lf_def coreCat : SCat ⇒ SCat := fun C => animaCat (coreAnima C)
  /-- The core is groupoidal because it is an anima.  Book context: Chapter 2 of the SCT book. -/
  lf_def coreGroupoid : (C : SCat) ⇒ GroupoidWitness (coreCat C) :=
    fun C => groupoidOfAnima (coreAnima C)
  /-- Inclusion of the core into the ambient category; Axiom G. -/
  lf_opaque coreIncl (C : SCat) : Functor (coreCat C) C
  /-- Objects of `C` parameterized by an anima/groupoid; Axiom G. -/
  syntax_abbrev GroupoidObject (A : Anima) (C : SCat) := Functor (animaCat A) (coreCat C)

extend_type_theory SCT where

  model_section Chapter2

  /-- The core inclusion is an embedding; split Definition 2.1.1/Axiom G data until the maximal
  subgroupoid property is represented internally. -/
  lf_opaque coreInclEmbedding (C : SCat) : Embedding (coreCat C) C (coreIncl C)

extend_type_theory SCT where

  model_section Chapter2

  /-- Lift an anima-parametrized object through the groupoid core; Axiom G.
  Book target: Axiom G, universal property of the groupoid core for anima-indexed sources. -/
  lf_opaque coreLift (A : Anima) (C : SCat) (F : Functor (animaCat A) C) :
    Functor (animaCat A) (coreCat C)

extend_type_theory SCT where

  model_section Chapter2

  /-- Lift a functor from a groupoid source through the core, via the anima represented by the
  groupoid.  Book context: Chapter 2 of the SCT book.
  -/
  lf_def coreLiftFromGroupoid : (G : SCat) ⇒ (C : SCat) ⇒ GroupoidWitness G ⇒
      Functor G C ⇒ Functor G (coreCat C) :=
    fun G C gG F => compFunctor G (animaCat (animaOfGroupoid G gG)) (coreCat C)
      (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
      (coreLift (animaOfGroupoid G gG) C
        (compFunctor (animaCat (animaOfGroupoid G gG)) G C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG)) F))

extend_type_theory SCT where

  model_section Chapter2

  /-- β comparison for the core lift; Axiom G.
  Book target: Axiom G, universal property of the groupoid core for anima-indexed sources. -/
  lf_opaque coreLiftBeta (A : Anima) (C : SCat) (F : Functor (animaCat A) C) :
    NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C
      (coreLift A C F) (coreIncl C)) F
  /-- Uniqueness of core lifts from anima-parametrized objects; Axiom G.
  Book target: Axiom G, universal property of the groupoid core for anima-indexed sources. -/
  lf_opaque coreLiftUniq (A : Anima) (C : SCat) (F : Functor (animaCat A) C)
    (K : Functor (animaCat A) (coreCat C))
    (β : NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C K
      (coreIncl C)) F) : NatIso (animaCat A) (coreCat C) K (coreLift A C F)
  /-- β comparison for a groupoid-source core lift, derived from the anima-source β rule and the
  groupoid/anima equivalence.  Book target: Axiom G specialized to groupoid sources. -/
  lf_def coreLiftFromGroupoidBeta : (G : SCat) ⇒ (C : SCat) ⇒
      (gG : GroupoidWitness G) ⇒ (F : Functor G C) ⇒
      NatIso G C
        (compFunctor G (coreCat C) C (coreLiftFromGroupoid G C gG F) (coreIncl C)) F :=
    fun G C gG F =>
      compNatIso G C
        (compFunctor G (coreCat C) C (coreLiftFromGroupoid G C gG F) (coreIncl C))
        (compFunctor G (animaCat (animaOfGroupoid G gG)) C
          (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
          (compFunctor (animaCat (animaOfGroupoid G gG)) (coreCat C) C
            (coreLift (animaOfGroupoid G gG) C
              (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)) F))
            (coreIncl C)))
        F
        (assocFunctor G (animaCat (animaOfGroupoid G gG)) (coreCat C) C
          (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
          (coreLift (animaOfGroupoid G gG) C
            (compFunctor (animaCat (animaOfGroupoid G gG)) G C
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG)) F))
          (coreIncl C))
        (compNatIso G C
          (compFunctor G (animaCat (animaOfGroupoid G gG)) C
            (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
            (compFunctor (animaCat (animaOfGroupoid G gG)) (coreCat C) C
              (coreLift (animaOfGroupoid G gG) C
                (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)) F))
              (coreIncl C)))
          (compFunctor G (animaCat (animaOfGroupoid G gG)) C
            (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
            (compFunctor (animaCat (animaOfGroupoid G gG)) G C
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG)) F))
          F
          (preWhiskerNatIso G (animaCat (animaOfGroupoid G gG)) C
            (catEquivForward G (animaCat (animaOfGroupoid G gG))
              (groupoid_anima_equiv G gG))
            (compFunctor (animaCat (animaOfGroupoid G gG)) (coreCat C) C
              (coreLift (animaOfGroupoid G gG) C
                (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)) F))
              (coreIncl C))
            (compFunctor (animaCat (animaOfGroupoid G gG)) G C
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG)) F)
            (coreLiftBeta (animaOfGroupoid G gG) C
              (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)) F)))
          (compNatIso G C
            (compFunctor G (animaCat (animaOfGroupoid G gG)) C
              (catEquivForward G (animaCat (animaOfGroupoid G gG)) (groupoid_anima_equiv G gG))
              (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)) F))
            (compFunctor G G C
              (compFunctor G (animaCat (animaOfGroupoid G gG)) G
                (catEquivForward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG))
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)))
              F)
            F
            (assocFunctorInv G (animaCat (animaOfGroupoid G gG)) G C
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              F)
            (compNatIso G C
              (compFunctor G G C
                (compFunctor G (animaCat (animaOfGroupoid G gG)) G
                  (catEquivForward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG))
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)))
                F)
              (compFunctor G G C (idFunctor G) F)
              F
              (postWhiskerNatIso G G C
                (compFunctor G (animaCat (animaOfGroupoid G gG)) G
                  (catEquivForward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG))
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)))
                (idFunctor G) F
                (catEquivUnit G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)))
              (leftUnitor G C F))))
  /-- Comparison needed to apply anima-source uniqueness to a groupoid-source lift. -/
  lf_def coreLiftFromGroupoidUniqBeta : (G : SCat) ⇒ (C : SCat) ⇒
      (gG : GroupoidWitness G) ⇒ (F : Functor G C) ⇒
      (L : Functor G (coreCat C)) ⇒
      NatIso G C (compFunctor G (coreCat C) C L (coreIncl C)) F ⇒
      NatIso (animaCat (animaOfGroupoid G gG)) C
        (compFunctor (animaCat (animaOfGroupoid G gG)) (coreCat C) C
          (compFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C)
            (catEquivBackward G (animaCat (animaOfGroupoid G gG))
              (groupoid_anima_equiv G gG)) L)
          (coreIncl C))
        (compFunctor (animaCat (animaOfGroupoid G gG)) G C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG)) F) :=
    fun G C gG F L β =>
      compNatIso (animaCat (animaOfGroupoid G gG)) C
        (compFunctor (animaCat (animaOfGroupoid G gG)) (coreCat C) C
          (compFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C)
            (catEquivBackward G (animaCat (animaOfGroupoid G gG))
              (groupoid_anima_equiv G gG)) L)
          (coreIncl C))
        (compFunctor (animaCat (animaOfGroupoid G gG)) G C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG))
          (compFunctor G (coreCat C) C L (coreIncl C)))
        (compFunctor (animaCat (animaOfGroupoid G gG)) G C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG)) F)
        (assocFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C) C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG)) L (coreIncl C))
        (preWhiskerNatIso (animaCat (animaOfGroupoid G gG)) G C
          (catEquivBackward G (animaCat (animaOfGroupoid G gG))
            (groupoid_anima_equiv G gG))
          (compFunctor G (coreCat C) C L (coreIncl C)) F β)
  /-- Uniqueness of groupoid-source core lifts, transported through the groupoid/anima
  equivalence.  Book target: Axiom G specialized to groupoid sources. -/
  lf_def coreLiftFromGroupoidUniq : (G : SCat) ⇒ (C : SCat) ⇒
      (gG : GroupoidWitness G) ⇒ (F : Functor G C) ⇒ (L : Functor G (coreCat C)) ⇒
      (β : NatIso G C (compFunctor G (coreCat C) C L (coreIncl C)) F) ⇒
      NatIso G (coreCat C) L (coreLiftFromGroupoid G C gG F) :=
    fun G C gG F L β =>
      compNatIso G (coreCat C)
        L
        (compFunctor G G (coreCat C) (idFunctor G) L)
        (coreLiftFromGroupoid G C gG F)
        (invNatIso G (coreCat C) (compFunctor G G (coreCat C) (idFunctor G) L) L
          (leftUnitor G (coreCat C) L))
        (compNatIso G (coreCat C)
          (compFunctor G G (coreCat C) (idFunctor G) L)
          (compFunctor G G (coreCat C)
            (compFunctor G (animaCat (animaOfGroupoid G gG)) G
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG)))
            L)
          (coreLiftFromGroupoid G C gG F)
          (postWhiskerNatIso G G (coreCat C)
            (idFunctor G)
            (compFunctor G (animaCat (animaOfGroupoid G gG)) G
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG)))
            L
            (invNatIso G G
              (compFunctor G (animaCat (animaOfGroupoid G gG)) G
                (catEquivForward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG))
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)))
              (idFunctor G)
              (catEquivUnit G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))))
          (compNatIso G (coreCat C)
            (compFunctor G G (coreCat C)
              (compFunctor G (animaCat (animaOfGroupoid G gG)) G
                (catEquivForward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG))
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)))
              L)
            (compFunctor G (animaCat (animaOfGroupoid G gG)) (coreCat C)
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (compFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C)
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)) L))
            (coreLiftFromGroupoid G C gG F)
            (assocFunctor G (animaCat (animaOfGroupoid G gG)) G (coreCat C)
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              L)
            (preWhiskerNatIso G (animaCat (animaOfGroupoid G gG)) (coreCat C)
              (catEquivForward G (animaCat (animaOfGroupoid G gG))
                (groupoid_anima_equiv G gG))
              (compFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C)
                (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                  (groupoid_anima_equiv G gG)) L)
              (coreLift (animaOfGroupoid G gG) C
                (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)) F))
              (coreLiftUniq (animaOfGroupoid G gG) C
                (compFunctor (animaCat (animaOfGroupoid G gG)) G C
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)) F)
                (compFunctor (animaCat (animaOfGroupoid G gG)) G (coreCat C)
                  (catEquivBackward G (animaCat (animaOfGroupoid G gG))
                    (groupoid_anima_equiv G gG)) L)
                (coreLiftFromGroupoidUniqBeta G C gG F L β)))))

extend_type_theory SCT where

  model_section Chapter2

  /-- Functorial action on groupoid cores, defined by lifting the composite out of the core.  Book
  context: Chapter 2 of the SCT book.
  -/
  lf_def coreFunctor : (C : SCat) ⇒ (D : SCat) ⇒ Functor C D ⇒
      Functor (coreCat C) (coreCat D) :=
    fun C D F => coreLiftFromGroupoid (coreCat C) D (coreGroupoid C)
      (compFunctor (coreCat C) C D (coreIncl C) F)
  /-- Lift a natural isomorphism through the core inclusion, using uniqueness of the target lift.
  Book target: Axiom G specialized to groupoid sources. -/
  lf_def coreLiftNatIsoFromGroupoid : (G : SCat) ⇒ (C : SCat) ⇒
      GroupoidWitness G ⇒ (L : Functor G (coreCat C)) ⇒ (M : Functor G (coreCat C)) ⇒
      NatIso G C (compFunctor G (coreCat C) C L (coreIncl C))
        (compFunctor G (coreCat C) C M (coreIncl C)) ⇒ NatIso G (coreCat C) L M :=
    fun G C gG L M α =>
      compNatIso G (coreCat C) L
        (coreLiftFromGroupoid G C gG (compFunctor G (coreCat C) C M (coreIncl C))) M
        (coreLiftFromGroupoidUniq G C gG
          (compFunctor G (coreCat C) C M (coreIncl C)) L α)
        (invNatIso G (coreCat C) M
          (coreLiftFromGroupoid G C gG (compFunctor G (coreCat C) C M (coreIncl C)))
          (coreLiftFromGroupoidUniq G C gG
            (compFunctor G (coreCat C) C M (coreIncl C)) M
            (idNatIso G C (compFunctor G (coreCat C) C M (coreIncl C)))))

extend_type_theory SCT where

  model_section Chapter2

  /-- Higher compatibility of a lifted core natural isomorphism with the original one; split
  Axiom G coherence data for the current core-universal-property interface. -/
  lf_opaque coreLiftNatIsoFromGroupoidBeta (G : SCat) (C : SCat) (gG : GroupoidWitness G)
    (L : Functor G (coreCat C)) (M : Functor G (coreCat C))
    (α : NatIso G C (compFunctor G (coreCat C) C L (coreIncl C))
      (compFunctor G (coreCat C) C M (coreIncl C))) :
    NatIsoIso G C (compFunctor G (coreCat C) C L (coreIncl C))
      (compFunctor G (coreCat C) C M (coreIncl C))
      (postWhiskerNatIso G (coreCat C) C L M (coreIncl C)
        (coreLiftNatIsoFromGroupoid G C gG L M α)) α

extend_type_theory SCT where

  model_section Chapter2

  /-- The core functor commutes with core inclusions, by the groupoid-source lift β rule.  Book
  context: Chapter 2 of the SCT book.
  -/
  lf_def coreFunctorBeta : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      NatIso (coreCat C) D
        (compFunctor (coreCat C) (coreCat D) D (coreFunctor C D F) (coreIncl D))
        (compFunctor (coreCat C) C D (coreIncl C) F) :=
    fun C D F => coreLiftFromGroupoidBeta (coreCat C) D (coreGroupoid C)
      (compFunctor (coreCat C) C D (coreIncl C) F)
  /-- The mapping anima is the core of the functor category.  Book context: Chapter 2 of the SCT
  book.
  -/
  lf_opaque mapAnimaCoreEquiv (C : SCat) (D : SCat) :
    CatEquiv (animaCat (mapAnima C D)) (coreCat (funCat C D))

extend_type_theory SCT where

  model_section Chapter2

  /-- Inverse to the core inclusion for a groupoid, obtained by the groupoid-source core lift. -/
  lf_def coreOfGroupoidBackward : (C : SCat) ⇒ GroupoidWitness C ⇒ Functor C (coreCat C) :=
    fun C gC => coreLiftFromGroupoid C C gC (idFunctor C)
  /-- Section comparison for the core inclusion of a groupoid. -/
  lf_def coreOfGroupoidSection : (C : SCat) ⇒ (gC : GroupoidWitness C) ⇒
      NatIso C C
        (compFunctor C (coreCat C) C (coreOfGroupoidBackward C gC) (coreIncl C))
        (idFunctor C) :=
    fun C gC => coreLiftFromGroupoidBeta C C gC (idFunctor C)
  /-- Comparison showing that the retraction candidate composes with the core inclusion as
  required to invoke core-lift uniqueness. -/
  lf_def coreOfGroupoidRetractionBeta : (C : SCat) ⇒ (gC : GroupoidWitness C) ⇒
      NatIso (coreCat C) C
        (compFunctor (coreCat C) (coreCat C) C
          (compFunctor (coreCat C) C (coreCat C) (coreIncl C)
            (coreOfGroupoidBackward C gC))
          (coreIncl C))
        (coreIncl C) :=
    fun C gC =>
      compNatIso (coreCat C) C
        (compFunctor (coreCat C) (coreCat C) C
          (compFunctor (coreCat C) C (coreCat C) (coreIncl C)
            (coreOfGroupoidBackward C gC))
          (coreIncl C))
        (compFunctor (coreCat C) C C (coreIncl C)
          (compFunctor C (coreCat C) C (coreOfGroupoidBackward C gC) (coreIncl C)))
        (coreIncl C)
        (assocFunctor (coreCat C) C (coreCat C) C (coreIncl C)
          (coreOfGroupoidBackward C gC) (coreIncl C))
        (compNatIso (coreCat C) C
          (compFunctor (coreCat C) C C (coreIncl C)
            (compFunctor C (coreCat C) C (coreOfGroupoidBackward C gC) (coreIncl C)))
          (compFunctor (coreCat C) C C (coreIncl C) (idFunctor C))
          (coreIncl C)
          (preWhiskerNatIso (coreCat C) C C (coreIncl C)
            (compFunctor C (coreCat C) C (coreOfGroupoidBackward C gC) (coreIncl C))
            (idFunctor C)
            (coreOfGroupoidSection C gC))
          (rightUnitor (coreCat C) C (coreIncl C)))
  /-- Retraction comparison for the core inclusion of a groupoid. -/
  lf_def coreOfGroupoidRetraction : (C : SCat) ⇒ (gC : GroupoidWitness C) ⇒
      NatIso (coreCat C) (coreCat C)
        (compFunctor (coreCat C) C (coreCat C) (coreIncl C)
          (coreOfGroupoidBackward C gC))
        (idFunctor (coreCat C)) :=
    fun C gC =>
      compNatIso (coreCat C) (coreCat C)
        (compFunctor (coreCat C) C (coreCat C) (coreIncl C)
          (coreOfGroupoidBackward C gC))
        (coreLiftFromGroupoid (coreCat C) C (coreGroupoid C) (coreIncl C))
        (idFunctor (coreCat C))
        (coreLiftFromGroupoidUniq (coreCat C) C (coreGroupoid C) (coreIncl C)
          (compFunctor (coreCat C) C (coreCat C) (coreIncl C)
            (coreOfGroupoidBackward C gC))
          (coreOfGroupoidRetractionBeta C gC))
        (invNatIso (coreCat C) (coreCat C) (idFunctor (coreCat C))
          (coreLiftFromGroupoid (coreCat C) C (coreGroupoid C) (coreIncl C))
          (coreLiftFromGroupoidUniq (coreCat C) C (coreGroupoid C) (coreIncl C)
            (idFunctor (coreCat C))
            (leftUnitor (coreCat C) C (coreIncl C))))
  /-- If `C` is a groupoid, its core inclusion is an equivalence, by Axiom G. -/
  lf_def coreOfGroupoidEquiv : (C : SCat) ⇒ GroupoidWitness C ⇒ CatEquiv (coreCat C) C :=
    fun C gC => catEquivOfSectionRetraction (coreCat C) C (coreIncl C)
      (coreOfGroupoidBackward C gC) (coreOfGroupoidSection C gC)
      (coreOfGroupoidBackward C gC) (coreOfGroupoidRetraction C gC)
      (coreOfGroupoidSection C gC) (coreOfGroupoidRetraction C gC)

extend_type_theory SCT where

  model_section Chapter2

  /-- Source-faithful comparison from `Map(C,D)` to the core of the functor category.  Book context:
  Chapter 2 of the SCT book.
  -/
  lf_def mapAnimaCoreForward : (C : SCat) ⇒ (D : SCat) ⇒
      Functor (animaCat (mapAnima C D)) (coreCat (funCat C D)) :=
    fun C D => catEquivForward (animaCat (mapAnima C D)) (coreCat (funCat C D))
      (mapAnimaCoreEquiv C D)
  /-- Inverse comparison from the functor-category core to `Map(C,D)`.  Book context: Chapter 2 of
  the SCT book.
  -/
  lf_def mapAnimaCoreBackward : (C : SCat) ⇒ (D : SCat) ⇒
      Functor (coreCat (funCat C D)) (animaCat (mapAnima C D)) :=
    fun C D => catEquivBackward (animaCat (mapAnima C D)) (coreCat (funCat C D))
      (mapAnimaCoreEquiv C D)
  /-- Unit for `Map(C,D) ≃ Fun(C,D)^≃`.  Book context: Chapter 2 of the SCT book. -/
  lf_def mapAnimaCoreUnit : (C : SCat) ⇒ (D : SCat) ⇒
      NatIso (animaCat (mapAnima C D)) (animaCat (mapAnima C D))
        (compFunctor (animaCat (mapAnima C D)) (coreCat (funCat C D))
          (animaCat (mapAnima C D)) (mapAnimaCoreForward C D) (mapAnimaCoreBackward C D))
        (idFunctor (animaCat (mapAnima C D))) :=
    fun C D => catEquivUnit (animaCat (mapAnima C D)) (coreCat (funCat C D))
      (mapAnimaCoreEquiv C D)
  /-- Counit for `Map(C,D) ≃ Fun(C,D)^≃`.  Book context: Chapter 2 of the SCT book. -/
  lf_def mapAnimaCoreCounit : (C : SCat) ⇒ (D : SCat) ⇒
      NatIso (coreCat (funCat C D)) (coreCat (funCat C D))
        (compFunctor (coreCat (funCat C D)) (animaCat (mapAnima C D))
          (coreCat (funCat C D)) (mapAnimaCoreBackward C D) (mapAnimaCoreForward C D))
        (idFunctor (coreCat (funCat C D))) :=
    fun C D => catEquivCounit (animaCat (mapAnima C D)) (coreCat (funCat C D))
      (mapAnimaCoreEquiv C D)

extend_type_theory SCT where

  model_section Chapter2

  /-- Functor categories into a groupoid are groupoids; source-facing Proposition 2.1.2(4) data
  until `GroupoidWitness` exposes the interval-characterization proof internally. -/
  lf_opaque funCatTargetGroupoid (C : SCat) (D : SCat) (gD : GroupoidWitness D) :
    GroupoidWitness (funCat C D)

extend_type_theory SCT where

  model_section Chapter2

  /-- For a groupoid target, the mapping anima and the functor category agree.  Book context:
  Chapter 2 of the SCT book.
  -/
  lf_def mapAnimaToFunctorTargetGroupoidEquiv : (A : SCat) ⇒ (G : SCat) ⇒
      GroupoidWitness G ⇒ CatEquiv (animaCat (mapAnima A G)) (funCat A G) :=
    fun A G gG => catEquivTrans (animaCat (mapAnima A G)) (coreCat (funCat A G))
      (funCat A G) (mapAnimaCoreEquiv A G)
      (coreOfGroupoidEquiv (funCat A G) (funCatTargetGroupoid A G gG))
  /-- The core of `[1]` is equivalent to two points; Axiom G.1. -/
  lf_opaque intervalCoreEndpointEquiv :
    CatEquiv (coprodCat terminalCat terminalCat) (coreCat intervalCat)

extend_type_theory SCT where

  model_section Chapter2

  /-- Product of cores comparison; source-facing Chapter 2 finite-limit closure data. -/
  lf_opaque coreProductEquiv (C : SCat) (D : SCat) :
    CatEquiv (coreCat (prodCat C D)) (prodCat (coreCat C) (coreCat D))
  /-- Pullback of cores comparison; source-facing Chapter 2 finite-limit closure data. -/
  lf_opaque corePullbackEquiv (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) :
    CatEquiv (coreCat (pullbackCat C D E F G))
      (pullbackCat (coreCat C) (coreCat D) (coreCat E)
        (coreFunctor C E F) (coreFunctor D E G))

extend_type_theory SCT where

  model_section Chapter2

  /-- The source-oriented endpoint map `⟨0,1⟩ : * ⊔ * → [1]^≃`.  Book context: Chapter 2 of the SCT
  book.
  -/
  lf_def intervalCoreEndpointMap :
      Functor (coprodCat terminalCat terminalCat) (coreCat intervalCat) :=
    catEquivForward (coprodCat terminalCat terminalCat) (coreCat intervalCat)
      intervalCoreEndpointEquiv
  /-- Three-point category used for the core of `[2]`.  Book context: Chapter 2 of the SCT book. -/
  lf_def threePointCat : SCat := coprodCat terminalCat (coprodCat terminalCat terminalCat)


namespace SCT

internal_defs where
  /-- A groupoid category is an anima-category.
  Book target: Axiom G, identifying groupoids with anima.
  This is derived from the groupoid/anima comparison and invariance under equivalence. -/
  def groupoid_is_anima_cat (C : SCat) (g : GroupoidWitness C) : isAnimaCat C :=
    equiv_to_anima_is_anima C (animaOfGroupoid C g) (groupoid_anima_equiv C g)

end SCT

extend_type_theory SCT where

  model_section Chapter2

  /-- The core of `[2]` is equivalent to three points; source-facing Axiom G.1 endpoint data. -/
  lf_opaque simplex2CoreEndpointEquiv : CatEquiv threePointCat (coreCat simplex2Cat)
  /-- Coproducts of groupoids are groupoids; source-facing Chapter 2 closure data. -/
  lf_opaque coprodGroupoid (C : SCat) (D : SCat)
    (gC : GroupoidWitness C) (gD : GroupoidWitness D) : GroupoidWitness (coprodCat C D)
  /-- Pullbacks of groupoids are groupoids; source-facing Chapter 2 closure data. -/
  lf_opaque pullbackGroupoid (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (gC : GroupoidWitness C) (gD : GroupoidWitness D) (gE : GroupoidWitness E) :
    GroupoidWitness (pullbackCat C D E F G)
  /-- The initial category is a groupoid; source-facing Chapter 2 closure data. -/
  lf_opaque initialGroupoid : GroupoidWitness initialCat

/-- Chapter 3: subcategories, localizations, realizations, joins, and slices; Axioms H--J.2. -/
extend_type_theory SCT where

  model_section Chapter3


  /-- A functor satisfying the book's replete subcategory criterion; Definition 3.1.2. -/
  syntax_sort SubcategoryWitness (A : SCat) (C : SCat) (i : Functor A C) : Type u

  /-- Subobjects of an anima; used for Axiom H morphism and object collections. -/
  syntax_sort AnimaSubobject (A : Anima) : Type (u+1)

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- The identity functor is a subcategory.
  Book target: Definition 3.1.2, the book criterion for a replete subcategory.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Verify the defining pullback/embedding condition internally. -/
  def idSubcategoryWitness (C : SCat) : SubcategoryWitness C C (idFunctor C) := sorry
  /-- The initial inclusion is a subcategory.
  Book target: Definition 3.1.2, the book criterion for a replete subcategory.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Verify the defining pullback/embedding condition internally. -/
  def initialSubcategoryWitness (C : SCat) :
      SubcategoryWitness initialCat C (initialElim C) := sorry
  /-- Every subcategory is an embedding.
  Book target: Definition 3.1.2, the book criterion for a replete subcategory.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Verify the defining pullback/embedding condition internally. -/
  def subcategoryWitnessEmbedding (A : SCat) (C : SCat) (i : Functor A C)
    (h : SubcategoryWitness A C i) : Embedding A C i := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Domain anima of a subobject; Axiom H. -/
  lf_opaque subobjectAnima (A : Anima) (P : AnimaSubobject A) : Anima
  /-- Inclusion functor of an anima subobject; Axiom H. -/
  lf_opaque subobjectIncl (A : Anima) (P : AnimaSubobject A) :
    Functor (animaCat (subobjectAnima A P)) (animaCat A)
  /-- Subobject inclusions are embeddings; Axiom H. -/
  lf_opaque subobjectInclEmbedding (A : Anima) (P : AnimaSubobject A) :
    Embedding (animaCat (subobjectAnima A P)) (animaCat A) (subobjectIncl A P)
  /-- The anima of morphisms of `C`, namely the core of `Fun([1], C)`; Axiom H. -/
  lf_def morphismAnima : SCat ⇒ Anima := fun C => coreAnima (funCat intervalCat C)
  /-- A morphism collection is a subobject of the anima of morphisms; Axiom H. -/
  syntax_abbrev MorphismCollection (C : SCat) := AnimaSubobject (morphismAnima C)
  /-- Underlying anima of a morphism collection.  Book context: Chapter 3 of the SCT book. -/
  lf_def morphismCollectionAnima : (C : SCat) ⇒ MorphismCollection C ⇒ Anima :=
    fun C W => subobjectAnima (morphismAnima C) W
  /-- Underlying groupoid/category of a morphism collection.  Book context: Chapter 3 of the SCT
  book.
  -/
  lf_def morphismCollectionCat : (C : SCat) ⇒ MorphismCollection C ⇒ SCat :=
    fun C W => animaCat (morphismCollectionAnima C W)
  /-- The underlying category of a morphism collection is a groupoid.
  Book context:Chapter 3 of the
  SCT book.
  -/
  lf_def morphismCollectionGroupoid : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      GroupoidWitness (morphismCollectionCat C W) :=
    fun C W => groupoidOfAnima (morphismCollectionAnima C W)
  /-- Inclusion of a morphism collection into the morphism anima `Map([1],C)`.  Book context:
  Chapter 3 of the SCT book.
  -/
  lf_def morphismCollectionIncl : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Functor (morphismCollectionCat C W) (coreCat (funCat intervalCat C)) :=
    fun C W => subobjectIncl (morphismAnima C) W
  /-- The morphism-collection inclusion is an embedding.
  Book context:Chapter 3 of the SCT book. -/
  lf_def morphismCollectionEmbedding : (C : SCat) ⇒ (W : MorphismCollection C) ⇒
      Embedding (morphismCollectionCat C W) (coreCat (funCat intervalCat C))
        (morphismCollectionIncl C W) :=
    fun C W => subobjectInclEmbedding (morphismAnima C) W
  /-- Object collections are subobjects of the core; Axiom H. -/
  syntax_abbrev ObjectCollection (C : SCat) := AnimaSubobject (coreAnima C)
  /-- Underlying anima of an object collection.  Book context: Chapter 3 of the SCT book. -/
  lf_def objectCollectionAnima : (C : SCat) ⇒ ObjectCollection C ⇒ Anima :=
    fun C P => subobjectAnima (coreAnima C) P
  /-- Underlying groupoid/category of an object collection.
  Book context:Chapter 3 of the SCT book.
  -/
  lf_def objectCollectionCat : (C : SCat) ⇒ ObjectCollection C ⇒ SCat :=
    fun C P => animaCat (objectCollectionAnima C P)
  /-- Inclusion of an object collection into the core.  Book context: Chapter 3 of the SCT book. -/
  lf_def objectCollectionIncl : (C : SCat) ⇒ (P : ObjectCollection C) ⇒
      Functor (objectCollectionCat C P) (coreCat C) :=
    fun C P => subobjectIncl (coreAnima C) P

  /-- Evidence that a morphism collection contains identities; Axiom H. -/
  syntax_sort containsIdentities (C : SCat) (W : MorphismCollection C) : Type u
  syntax_sort_role containsIdentities : side_structure
  /-- Evidence that a morphism collection is closed under composition; Axiom H. -/
  syntax_sort closedUnderComposition (C : SCat) (W : MorphismCollection C) : Type u
  syntax_sort_role closedUnderComposition : side_structure

  /-- The collection of all morphisms; Axiom H and Axiom J. -/
  lf_opaque allMorphisms (C : SCat) : MorphismCollection C
  /-- The collection of all morphisms contains identities.
  Book target: Axiom H and Definition 3.1.6, where the all-morphisms collection is a closed
  morphism collection.
  Status: remaining T-shaped model-facing evidence field.  To make this book-faithful, prove it from
  the definition of `allMorphisms` instead of exposing a separate model obligation. -/
  lf_opaque all_morphisms_contains_identities (C : SCat) :
    containsIdentities C (allMorphisms C)
  /-- The collection of all morphisms is closed under composition.
  Book target: Axiom H and Definition 3.1.6, where the all-morphisms collection is a closed
  morphism collection.
  Status: remaining T-shaped model-facing evidence field.  To make this book-faithful, prove it from
  the definition of `allMorphisms` and Segal composition rather than exposing a separate model
  obligation. -/
  lf_opaque all_morphisms_closed (C : SCat) :
    closedUnderComposition C (allMorphisms C)

  /-- Subcategory determined by a morphism collection; Axiom H. -/
  lf_opaque subcategory (C : SCat) (W : MorphismCollection C) : SCat
  /-- Inclusion of a subcategory; Axiom H. -/
  lf_opaque subcategoryIncl (C : SCat) (W : MorphismCollection C) :
    Functor (subcategory C W) C
  /-- The generated subcategory inclusion is a subcategory; Axiom H. -/
  lf_opaque subcategoryInclWitness (C : SCat) (W : MorphismCollection C)
    (ids : containsIdentities C W) (comp : closedUnderComposition C W) :
    SubcategoryWitness (subcategory C W) C (subcategoryIncl C W)
  /-- Evidence that a functor's morphisms factor through a chosen collection; Axiom H. -/
  syntax_sort PreservesMorphismCollection (D : SCat) (C : SCat)
    (W : MorphismCollection C) (F : Functor D C) : Type u
  syntax_sort_role PreservesMorphismCollection : side_structure

extend_type_theory SCT where

  model_section Chapter3

  /-- Full subcategory determined by an object collection; Axiom H.
  Book target: §3.1, full subcategories determined by object collections. -/
  lf_opaque fullSubcategory (C : SCat) (P : ObjectCollection C) : SCat
  /-- Inclusion of a full subcategory; Axiom H.
  Book target: §3.1, full subcategories determined by object collections. -/
  lf_opaque fullSubcategoryIncl (C : SCat) (P : ObjectCollection C) :
    Functor (fullSubcategory C P) C
  /-- The full-subcategory inclusion is a subcategory; Axiom H.
  Book target: §3.1, full subcategories determined by object collections. -/
  lf_opaque fullSubcategoryInclWitness (C : SCat) (P : ObjectCollection C) :
    SubcategoryWitness (fullSubcategory C P) C (fullSubcategoryIncl C P)
  /-- The core of a full subcategory is the specified object collection.
  Book target: §3.1, full subcategories determined by object collections. -/
  lf_opaque fullSubcategoryCoreEquiv (C : SCat) (P : ObjectCollection C) :
    CatEquiv (coreCat (fullSubcategory C P)) (objectCollectionCat C P)
  /-- The full subcategory spanned by all objects is equivalent to the ambient category.
  Book target: §3.1, full subcategories determined by object collections. -/
  lf_opaque fullSubcategoryAllObjectsEquiv (C : SCat) (P : ObjectCollection C)
    (hAll : CatEquiv (objectCollectionCat C P) (coreCat C)) :
      CatEquiv (fullSubcategory C P) C

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Object collection of invertible arrows in `Fun([1], C)`.  This is the remaining
  source-shaped placeholder for the subobject comprehension needed to build `Iso(C)` from explicit
  invertible-arrow data.
  -/
  lf_opaque invertibleMorphismObjects (C : SCat) : ObjectCollection (funCat intervalCat C)
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
  /-- Packaged Rezk completeness equivalence; Axiom F. -/
  lf_opaque rezkEquiv (C : SCat) : CatEquiv C (isoCat C)
  /-- Identity-isomorphism functor into the isomorphism category; derived from Rezk completeness.
  Book context: Chapter 1 of the SCT book.
  -/
  lf_def identityIsoFunctor : (C : SCat) ⇒ Functor C (isoCat C) :=
    fun C => catEquivForward C (isoCat C) (rezkEquiv C)
  /-- Projection from isomorphisms back to objects; derived from Rezk completeness.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_def isoProjectionFunctor : (C : SCat) ⇒ Functor (isoCat C) C :=
    fun C => catEquivBackward C (isoCat C) (rezkEquiv C)
  /-- Unit for the Rezk equivalence; derived from the packaged equivalence.  Book context: Chapter 1
  of the SCT book.
  -/
  lf_def rezkUnit : (C : SCat) ⇒
      NatIso C C
        (compFunctor C (isoCat C) C (identityIsoFunctor C) (isoProjectionFunctor C))
        (idFunctor C) :=
    fun C => catEquivUnit C (isoCat C) (rezkEquiv C)
  /-- Counit for the Rezk equivalence; derived from the packaged equivalence.  Book context:
  Chapter 1 of the SCT book.
  -/
  lf_def rezkCounit : (C : SCat) ⇒
      NatIso (isoCat C) (isoCat C)
        (compFunctor (isoCat C) C (isoCat C)
          (isoProjectionFunctor C) (identityIsoFunctor C))
        (idFunctor (isoCat C)) :=
    fun C => catEquivCounit C (isoCat C) (rezkEquiv C)

extend_type_theory SCT where

  model_section Chapter3

  /-- The generated subcategory inclusion preserves the defining morphism collection.
  Book target: Axiom H(1), the first universal property of the subcategory generated by a closed
  morphism collection.
  Status: remaining T-shaped model-facing evidence field.  To make this book-faithful, prove it from
  the construction of `subcategory` and `subcategoryIncl`. -/
  lf_opaque subcategoryInclPreserves (C : SCat) (W : MorphismCollection C) :
    PreservesMorphismCollection (subcategory C W) C W (subcategoryIncl C W)
  /-- Universal lift through a subcategory; Axiom H. -/
  lf_opaque subcategoryLift (D : SCat) (C : SCat) (W : MorphismCollection C)
    (ids : containsIdentities C W) (comp : closedUnderComposition C W)
    (F : Functor D C) (h : PreservesMorphismCollection D C W F) :
    Functor D (subcategory C W)
  /-- β comparison for the subcategory lift; Axiom H. -/
  lf_opaque subcategoryLiftBeta (D : SCat) (C : SCat) (W : MorphismCollection C)
    (ids : containsIdentities C W) (comp : closedUnderComposition C W)
    (F : Functor D C) (h : PreservesMorphismCollection D C W F) :
    NatIso D C
      (compFunctor D (subcategory C W) C
        (subcategoryLift D C W ids comp F h) (subcategoryIncl C W))
      F
  /-- Uniqueness of subcategory lifts over `C`; Axiom H. -/
  lf_opaque subcategoryLiftUniq (D : SCat) (C : SCat) (W : MorphismCollection C)
    (ids : containsIdentities C W) (comp : closedUnderComposition C W)
    (F : Functor D C) (h : PreservesMorphismCollection D C W F)
    (K : Functor D (subcategory C W))
    (β : NatIso D C (compFunctor D (subcategory C W) C K (subcategoryIncl C W)) F) :
    NatIso D (subcategory C W) K (subcategoryLift D C W ids comp F h)
  /-- Evidence that a functor lands in a chosen object collection; Axiom H. -/
  syntax_sort LandsInObjectCollection (D : SCat) (C : SCat)
    (P : ObjectCollection C) (F : Functor D C) : Type u
  syntax_sort_role LandsInObjectCollection : side_structure
  /-- The full-subcategory inclusion lands in its defining object collection.
  Book target: §3.1, full subcategories determined by object collections.
  Status: remaining T-shaped model-facing evidence field.  To make this book-faithful, construct
  full subcategories from Axiom H and prove the landing evidence internally. -/
  lf_opaque fullSubcategoryInclLands (C : SCat) (P : ObjectCollection C) :
    LandsInObjectCollection (fullSubcategory C P) C P (fullSubcategoryIncl C P)
  /-- Universal lift through a full subcategory; Axiom H. -/
  lf_opaque fullSubcategoryLift (D : SCat) (C : SCat) (P : ObjectCollection C)
    (F : Functor D C) (h : LandsInObjectCollection D C P F) :
    Functor D (fullSubcategory C P)
  /-- β comparison for the full-subcategory lift; Axiom H. -/
  lf_opaque fullSubcategoryLiftBeta (D : SCat) (C : SCat) (P : ObjectCollection C)
    (F : Functor D C) (h : LandsInObjectCollection D C P F) :
    NatIso D C
      (compFunctor D (fullSubcategory C P) C
        (fullSubcategoryLift D C P F h) (fullSubcategoryIncl C P))
      F
  /-- Uniqueness of lifts through full subcategories; Axiom H. -/
  lf_opaque fullSubcategoryLiftUniq (D : SCat) (C : SCat) (P : ObjectCollection C)
    (F : Functor D C) (h : LandsInObjectCollection D C P F)
    (K : Functor D (fullSubcategory C P))
    (β : NatIso D C (compFunctor D (fullSubcategory C P) C K
      (fullSubcategoryIncl C P)) F) :
    NatIso D (fullSubcategory C P) K (fullSubcategoryLift D C P F h)

  /-- Evidence that a functor sends a morphism collection to isomorphisms; Axiom I. -/
  syntax_sort InvertsMorphismCollection (C : SCat) (D : SCat)
    (W : MorphismCollection C) (F : Functor C D) : Type u
  syntax_sort_role InvertsMorphismCollection : side_structure
  /-- Localization at a morphism collection; Axiom I. -/
  lf_opaque localizationCat (C : SCat) (W : MorphismCollection C) : SCat

extend_type_theory SCT where

  model_section Chapter3

  /-- Object collection of functors that invert a morphism collection.  This is the remaining
  source-shaped placeholder for the comprehension needed in Definition 3.3.2. -/
  lf_opaque invertingFunctorObjects (C : SCat) (D : SCat) (W : MorphismCollection C) :
    ObjectCollection (funCat C D)
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
  To make this book-faithful: prove that all morphisms in a groupoid are invertible, then show the
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
  /-- Descend a functor that inverts the localized morphisms; Axiom I. -/
  lf_opaque localizationDesc (C : SCat) (W : MorphismCollection C) (D : SCat)
    (F : Functor C D) (h : InvertsMorphismCollection C D W F) :
    Functor (localizationCat C W) D
  /-- β comparison for localization descent; Axiom I. -/
  lf_opaque localizationDescBeta (C : SCat) (W : MorphismCollection C) (D : SCat)
    (F : Functor C D) (h : InvertsMorphismCollection C D W F) :
    NatIso C D
      (compFunctor C (localizationCat C W) D
        (localizationFunctor C W) (localizationDesc C W D F h))
      F
  /-- Uniqueness of localization descents; Axiom I. -/
  lf_opaque localizationDescUniq (C : SCat) (W : MorphismCollection C) (D : SCat)
    (F : Functor C D) (h : InvertsMorphismCollection C D W F)
    (K : Functor (localizationCat C W) D)
    (β : NatIso C D (compFunctor C (localizationCat C W) D
      (localizationFunctor C W) K) F) :
    NatIso (localizationCat C W) D K (localizationDesc C W D F h)
  /-- Universal equivalence `Fun(C[W^{-1}],D) ≃ Fun^W(C,D)` for localizations.  Book context:
  Chapter 3 of the SCT book.
  -/
  lf_opaque localizationUniversalEquiv (C : SCat) (W : MorphismCollection C) (D : SCat) :
    CatEquiv (funCat (localizationCat C W) D) (invertingFunctorCat C D W)
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
  /-- Pushout-square presentation of localization.
  Book target: Remark 3.3.8, localization presented by a pushout square.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Derive from Axiom I and the inverting-functor universal property. -/
  def localizationPushoutSquare (C : SCat) (W : MorphismCollection C) :
    PushoutSquare (prodCat intervalCat (morphismCollectionCat C W)) C
      (morphismCollectionCat C W) (localizationCat C W)
      (morphismCollectionArrowFunctor C W) (prodPr2 intervalCat (morphismCollectionCat C W))
      (localizationFunctor C W) (localizationCollectionFunctor C W) := sorry

end SCT

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
  To make this book-faithful: prove that localization at all morphisms is groupoidal and transport
  it to an anima via `groupoid_is_anima_cat`.
  -/
  def geometric_realization_is_anima (C : SCat) : isAnimaCat (geometricRealization C) := sorry

  /-- Categories over a base, used for exponentiable functors.
  Book target: Definition 3.5.4, the over-category `Cat/C` of categories over a base.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Construct as the appropriate slice/fiber of a functor category. -/
  def overCat (B : SCat) : SCat := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Dependent product along a map over a base.  Book context: Chapter 3 of the SCT book. -/
  lf_opaque dependentProductOverCat (A : SCat) (B : SCat) (E : SCat)
    (u : Functor A B) (p : Functor E A) : SCat
  /-- Projection of a dependent product over the codomain.  Book context: Chapter 3 of the SCT book.
  -/
  lf_opaque dependentProductOverProjection (A : SCat) (B : SCat) (E : SCat)
    (u : Functor A B) (p : Functor E A) : Functor (dependentProductOverCat A B E u p) B
  /-- Exponentiable functor witness; Definition 3.5.7. -/
  syntax_sort ExponentiableFunctor (A : SCat) (B : SCat) (u : Functor A B) : Type u

  /-- Join of synthetic categories; Axioms J.1 and J.2. -/
  lf_opaque joinCat (C : SCat) (D : SCat) : SCat

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Pullback/reindexing functor between over-categories.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove from exponentiability of the base functor. -/
  def overPullbackFunctor (A : SCat) (B : SCat) (u : Functor A B) :
    Functor (overCat B) (overCat A) := sorry
  /-- Dependent product functor right adjoint to pullback for an exponentiable functor.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove from exponentiability of the base functor. -/
  def dependentProductFunctor (A : SCat) (B : SCat)
    (u : Functor A B) (exp : ExponentiableFunctor A B u) : Functor (overCat A) (overCat B) := sorry
  /-- Beck-Chevalley comparison for dependent products; Construction 3.5.6.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove from exponentiability of the base functor. -/
  def dependentProductBeckChevalley (A : SCat) (B : SCat) (A' : SCat) (B' : SCat)
    (u : Functor A B) (u' : Functor A' B') (f : Functor A' A) (g : Functor B' B)
    (exp : ExponentiableFunctor A B u) (exp' : ExponentiableFunctor A' B' u') :
    NatTrans (overCat A) (overCat B')
      (compFunctor (overCat A) (overCat B) (overCat B')
        (dependentProductFunctor A B u exp) (overPullbackFunctor B' B g))
      (compFunctor (overCat A) (overCat A') (overCat B')
        (overPullbackFunctor A' A f) (dependentProductFunctor A' B' u' exp')) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Left inclusion into a join; Axiom J.1. -/
  lf_opaque joinInl (C : SCat) (D : SCat) : Functor C (joinCat C D)
  /-- Right inclusion into a join; Axiom J.1. -/
  lf_opaque joinInr (C : SCat) (D : SCat) : Functor D (joinCat C D)
  /-- Join as the pushout of `C ← ∅ → D`; Axiom J.1. -/
  lf_opaque joinPushoutSquare (C : SCat) (D : SCat) :
    PushoutSquare initialCat C D (joinCat C D)
      (initialElim C) (initialElim D) (joinInl C D) (joinInr C D)
  /-- Mapping-out universal property of joins; Axiom J.1. -/
  lf_opaque joinMappingOutEquiv (C : SCat) (D : SCat) (E : SCat) :
    CatEquiv (funCat (joinCat C D) E) (prodCat (funCat C E) (funCat D E))
  /-- Join eliminator/universal descender; Axioms J.1 and J.2. -/
  lf_opaque joinDesc (C : SCat) (D : SCat) (E : SCat)
    (L : Functor C E) (R : Functor D E) : Functor (joinCat C D) E
  /-- Left β comparison for the join descender; Axiom J.2. -/
  lf_opaque joinBetaLeft (C : SCat) (D : SCat) (E : SCat)
    (L : Functor C E) (R : Functor D E) :
    NatIso C E (compFunctor C (joinCat C D) E (joinInl C D) (joinDesc C D E L R)) L
  /-- Right β comparison for the join descender; Axiom J.2. -/
  lf_opaque joinBetaRight (C : SCat) (D : SCat) (E : SCat)
    (L : Functor C E) (R : Functor D E) :
    NatIso D E (compFunctor D (joinCat C D) E (joinInr C D) (joinDesc C D E L R)) R
  /-- Uniqueness of join descenders from endpoint restrictions; Axiom J.2. -/
  lf_opaque joinDescUniq (C : SCat) (D : SCat) (E : SCat)
    (L : Functor C E) (R : Functor D E) (K : Functor (joinCat C D) E)
    (α : NatIso C E (compFunctor C (joinCat C D) E (joinInl C D) K) L)
    (β : NatIso D E (compFunctor D (joinCat C D) E (joinInr C D) K) R) :
    NatIso (joinCat C D) E K (joinDesc C D E L R)
  /-- Left cone; Axioms J.1 and J.2. -/
  lf_def leftConeCat : SCat ⇒ SCat := fun C => joinCat simplex0Cat C
  /-- Right cone; Axioms J.1 and J.2. -/
  lf_def rightConeCat : SCat ⇒ SCat := fun C => joinCat C simplex0Cat
  /-- Forward comparison `[1] → [0] ★ [0]`; Axiom J.1. -/
  lf_opaque intervalJoinForward : Functor intervalCat (joinCat simplex0Cat simplex0Cat)
  /-- Backward comparison `[0] ★ [0] → [1]`; Axiom J.1. -/
  lf_opaque intervalJoinBackward : Functor (joinCat simplex0Cat simplex0Cat) intervalCat
  /-- Unit for the interval/join comparison; Axiom J.1. -/
  lf_opaque intervalJoinUnit :
    NatIso intervalCat intervalCat
      (compFunctor intervalCat (joinCat simplex0Cat simplex0Cat) intervalCat
        intervalJoinForward intervalJoinBackward)
      (idFunctor intervalCat)
  /-- Counit for the interval/join comparison; Axiom J.1. -/
  lf_opaque intervalJoinCounit :
    NatIso (joinCat simplex0Cat simplex0Cat) (joinCat simplex0Cat simplex0Cat)
      (compFunctor (joinCat simplex0Cat simplex0Cat) intervalCat
        (joinCat simplex0Cat simplex0Cat) intervalJoinBackward intervalJoinForward)
      (idFunctor (joinCat simplex0Cat simplex0Cat))
  /-- The walking interval is the join of two points; Axiom J.1. -/
  lf_def interval_join_equiv : CatEquiv intervalCat (joinCat simplex0Cat simplex0Cat) :=
    catEquivOfData intervalCat (joinCat simplex0Cat simplex0Cat)
      intervalJoinForward intervalJoinBackward intervalJoinUnit intervalJoinCounit
  /-- Source-shaped category for the mapping-in dependent-product side of Axiom J.2. -/
  lf_opaque joinDependentProductCat (C : SCat) (D : SCat) (E : SCat) : SCat
  /-- Join-dependent-product universal property; Axiom J.2. -/
  lf_opaque joinDependentProductEquiv (C : SCat) (D : SCat) (E : SCat) :
    CatEquiv (funCat E (joinCat C D)) (joinDependentProductCat C D E)

  /-- The 3-simplex, defined as the join of a point and `[2]`.  Book context: Chapter 3 of the SCT
  book.
  -/
  lf_def simplex3Cat : SCat := joinCat simplex0Cat simplex2Cat

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where




  /-- Relative join over a common base.
  Book target: Proposition 3.5.15 and Corollary 3.5.16, relative joins as dependent-product
  constructions.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Define from dependent products and the ordinary join interface. -/
  def relativeJoinCat (B : SCat) (C : SCat) (D : SCat)
    (p : Functor C B) (q : Functor D B) : SCat := sorry
  /-- Left inclusion into a relative join.
  Book target: Proposition 3.5.15 and Corollary 3.5.16, relative joins as dependent-product
  constructions.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Define from dependent products and the ordinary join interface. -/
  def relativeJoinInl (B : SCat) (C : SCat) (D : SCat)
    (p : Functor C B) (q : Functor D B) : Functor C (relativeJoinCat B C D p q) := sorry
  /-- Right inclusion into a relative join.
  Book target: Proposition 3.5.15 and Corollary 3.5.16, relative joins as dependent-product
  constructions.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Define from dependent products and the ordinary join interface. -/
  def relativeJoinInr (B : SCat) (C : SCat) (D : SCat)
    (p : Functor C B) (q : Functor D B) : Functor D (relativeJoinCat B C D p q) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter3

  /-- Simplices are generated by iterated joins of points; definitional in this interface.  Book
  context: Chapter 3 of the SCT book.
  -/
  lf_def simplex3JoinEquiv : CatEquiv simplex3Cat (joinCat simplex0Cat simplex2Cat) :=
    catEquivRefl (joinCat simplex0Cat simplex2Cat)

  /-- Source-faithful slice `C/F`; objects are arrows `const_x → F`.  Book context: Chapter 3 of the
  SCT book.
  -/
  lf_def sliceOverCat : (A : SCat) ⇒ (C : SCat) ⇒ Functor A C ⇒ SCat :=
    fun A C F => pullbackCat (funCat intervalCat C) A C (targetFunctor C) F
  /-- Projection selecting the vertex object of a slice object.  Book context: Chapter 3 of the SCT
  book.
  -/
  lf_def sliceOverVertex : (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒
      Functor (sliceOverCat A C F) C :=
    fun A C F => compFunctor (sliceOverCat A C F) (funCat intervalCat C) C
      (pullbackPr1 (funCat intervalCat C) A C (targetFunctor C) F) (sourceFunctor C)
  /-- Projection from `C/F` to the diagram shape.  Book context: Chapter 3 of the SCT book. -/
  lf_def sliceOverDiagram : (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒
      Functor (sliceOverCat A C F) A :=
    fun A C F => pullbackPr2 (funCat intervalCat C) A C (targetFunctor C) F
  /-- Dual slice `F/C`; objects are arrows `F → const_x`.  Book context: Chapter 3 of the SCT book.
  -/
  lf_def cosliceCat : (A : SCat) ⇒ (C : SCat) ⇒ Functor A C ⇒ SCat :=
    fun A C F => pullbackCat A (funCat intervalCat C) C F (sourceFunctor C)
  /-- Projection selecting the vertex object of a coslice object.
  Book context:Chapter 3 of the SCT
  book.
  -/
  lf_def cosliceVertex : (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒
      Functor (cosliceCat A C F) C :=
    fun A C F => compFunctor (cosliceCat A C F) (funCat intervalCat C) C
      (pullbackPr2 A (funCat intervalCat C) C F (sourceFunctor C)) (targetFunctor C)




/-- Chapter 4: synthetic categories in context and dependent sums; Axiom K. -/
extend_type_theory SCT where

  model_section Chapter4


  /-- Category in context `Γ`; Axiom K.1. -/
  syntax_sort ContextCat (Γ : SCat) : Type (u+1)
  /-- Functor in a fixed context; Axiom K.1. -/
  syntax_sort ContextFunctor (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) : Type u
  /-- Natural isomorphism in context; Axiom K.1. -/
  syntax_sort ContextNatIso (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ)
    (F : ContextFunctor Γ C D) (G : ContextFunctor Γ C D) : Type u
  /-- Equivalence in context; Axiom K.1. -/
  syntax_sort ContextCatEquiv (Γ : SCat) (C : ContextCat Γ) (D : ContextCat Γ) : Type u
  /-- Pullback-square predicate in a fixed context.  Book context: Chapter 4 of the SCT book. -/
  syntax_sort ContextPullbackSquare (Γ : SCat)
    (A : ContextCat Γ) (B : ContextCat Γ) (C : ContextCat Γ) (D : ContextCat Γ)
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
    (F : Functor C D) (G : Functor C D) (α : NatIso C D F G) :
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
      (reindexContextCat Θ Γ (compFunctor Θ Δ Γ v u) C)
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
  syntax_sort ContextMorphismCollection (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : Type (u+1)
  /-- Contextual object collection in a groupoidal context.
  Book context:Chapter 4 of the SCT book.
  -/
  syntax_sort ContextObjectCollection (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : Type (u+1)
  /-- Contextual subcategories in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextSubcategory (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (W : ContextMorphismCollection Γ gΓ C) : ContextCat Γ
  /-- Contextual localizations in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextLocalization (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (W : ContextMorphismCollection Γ gΓ C) : ContextCat Γ
  /-- Contextual geometric realizations in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextGeometricRealization (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) : ContextCat Γ
  /-- Contextual joins in groupoidal contexts; Axiom K.2. -/
  lf_opaque contextJoinCat (Γ : SCat) (gΓ : GroupoidalContext Γ)
    (C : ContextCat Γ) (D : ContextCat Γ) : ContextCat Γ
  /-- Contextual slice categories in groupoidal contexts; Axiom K.2. -/
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
    NatIso Γ Γ
      (compFunctor Γ (sigmaCat Γ (weakenContextCat Γ terminalCat)) Γ
        (sigmaLift Γ Γ (idFunctor Γ) (weakenContextCat Γ terminalCat))
        (sigmaProjection Γ (weakenContextCat Γ terminalCat)))
      (idFunctor Γ)

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
  To make this book-faithful: Construct the equivalence using dependent sums and reindexing. -/
  def contextCategoryCat (Γ : SCat) : SCat := sorry
  /-- Object of `contextCategoryCat Γ` corresponding to a contextual category.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Construct the equivalence using dependent sums and reindexing. -/
  def contextCategoryObject (Γ : SCat) (C : ContextCat Γ) : Obj (contextCategoryCat Γ) := sorry

end SCT

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Contextual category associated to a category over `Γ`.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Construct the equivalence using dependent sums and reindexing. -/
  def overFunctorToContext (Γ : SCat) (E : SCat) (p : Functor E Γ) : ContextCat Γ := sorry
  /-- Equivalence between contextual categories over `Γ` and categories over `Γ`.
  Book target: Proposition 4.2.16, correspondence between categories in context `Γ` and categories
  over `Γ`.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Construct the equivalence using dependent sums and reindexing. -/
  def contextOverCorrespondence (Γ : SCat) : CatEquiv (contextCategoryCat Γ) (overCat Γ) := sorry



end SCT

/-- Chapter 5: cartesian and cocartesian fibrations; Axiom L. -/
extend_type_theory SCT where

  model_section Chapter5


  /-- Isofibration witness for the base condition in Definition 5.6.1. -/
  syntax_sort IsofibrationWitness (E : SCat) (B : SCat) (p : Functor E B) : Type u
  /-- Chapter 5 fibration vocabulary is the book's isofibration condition. -/
  syntax_abbrev Fibration (E : SCat) (B : SCat) (p : Functor E B) := IsofibrationWitness E B p
  /-- A section of a functor that is left adjoint to it.
  Book context:Chapter 5 of the SCT book. -/
  syntax_sort LeftAdjointSection (C : SCat) (D : SCat) (p : Functor C D) : Type u
  /-- A section of a functor that is right adjoint to it.  Book context: Chapter 5 of the SCT book.
  -/
  syntax_sort RightAdjointSection (C : SCat) (D : SCat) (p : Functor C D) : Type u
  /-- Underlying section functor of a left-adjoint-section witness.  Book context: Chapter 5 of the
  SCT book.
  -/
  lf_opaque leftAdjointSectionFunctor (C : SCat) (D : SCat) (p : Functor C D)
    (s : LeftAdjointSection C D p) : Functor D C
  /-- Underlying section functor of a right-adjoint-section witness.  Book context: Chapter 5 of the
  SCT book.
  -/
  lf_opaque rightAdjointSectionFunctor (C : SCat) (D : SCat) (p : Functor C D)
    (s : RightAdjointSection C D p) : Functor D C

  /-- Directed/lax pullback of `f : A → C` and `g : B → C`; triples `(a,b,f a → g b)`.  Book
  context: Chapter 5 of the SCT book.
  -/
  lf_opaque directedPullbackCat (A : SCat) (B : SCat) (C : SCat)
    (f : Functor A C) (g : Functor B C) : SCat
  /-- First projection from a directed pullback.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque directedPullbackPr1 (A : SCat) (B : SCat) (C : SCat)
    (f : Functor A C) (g : Functor B C) : Functor (directedPullbackCat A B C f g) A
  /-- Second projection from a directed pullback.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque directedPullbackPr2 (A : SCat) (B : SCat) (C : SCat)
    (f : Functor A C) (g : Functor B C) : Functor (directedPullbackCat A B C f g) B
  /-- Arrow component of a directed pullback.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque directedPullbackArrow (A : SCat) (B : SCat) (C : SCat)
    (f : Functor A C) (g : Functor B C) :
    Functor (directedPullbackCat A B C f g) (funCat intervalCat C)
  /-- Directed evaluation at sources of arrows in the total category.
  Book context:Chapter 5 of the
  SCT book.
  -/
  lf_opaque directedEval0 (E : SCat) (B : SCat) (p : Functor E B) :
    Functor (funCat intervalCat E) (directedPullbackCat E B B p (idFunctor B))
  /-- Directed evaluation at targets of arrows in the total category.
  Book context:Chapter 5 of the
  SCT book.
  -/
  lf_opaque directedEval1 (E : SCat) (B : SCat) (p : Functor E B) :
    Functor (funCat intervalCat E) (directedPullbackCat B E B (idFunctor B) p)
  /-- Cartesian structure on a fibration, represented by a right adjoint section of `directedEval1`.
  Book context: Chapter 5 of the SCT book.
  -/
  syntax_abbrev CartesianFibrationWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) :=
    RightAdjointSection (funCat intervalCat E)
      (directedPullbackCat B E B (idFunctor B) p) (directedEval1 E B p)
  /-- Cocartesian structure on a fibration, represented by a left adjoint section of
  `directedEval0`. Book context: Chapter 5 of the SCT book.
  -/
  syntax_abbrev CocartesianFibrationWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) :=
    LeftAdjointSection (funCat intervalCat E)
      (directedPullbackCat E B B p (idFunctor B)) (directedEval0 E B p)
  /-- Left-fibration structure; Chapter 5. -/
  syntax_sort LeftFibrationWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) : Type u

extend_type_theory SCT where

  model_section Chapter5

  /-- Source fibration of a category; Chapter 5 source-fibration structure data. -/
  lf_opaque sourceFibration (C : SCat) : Fibration (funCat intervalCat C) C (sourceFunctor C)
  /-- Target fibration of a category; Chapter 5 target-fibration structure data. -/
  lf_opaque targetFibration (C : SCat) : Fibration (funCat intervalCat C) C (targetFunctor C)

extend_type_theory SCT where

  model_section Chapter5

  /-- Right-fibration structure; Chapter 5. -/
  syntax_sort RightFibrationWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) : Type u
  /-- Left fibrations are equivalently those with `directedEval0` an equivalence.  Book context:
  Chapter 5 of the SCT book.
  -/
  lf_opaque leftFibrationEvalEquiv (E : SCat) (B : SCat) (p : Functor E B)
      (fib : Fibration E B p) (left : LeftFibrationWitness E B p fib) :
      CatEquiv (funCat intervalCat E) (directedPullbackCat E B B p (idFunctor B))
  /-- Right fibrations are equivalently those with `directedEval1` an equivalence.  Book context:
  Chapter 5 of the SCT book.
  -/
  lf_opaque rightFibrationEvalEquiv (E : SCat) (B : SCat) (p : Functor E B)
      (fib : Fibration E B p) (right : RightFibrationWitness E B p fib) :
      CatEquiv (funCat intervalCat E) (directedPullbackCat B E B (idFunctor B) p)
  /-- Category of covariant lifts for `directedEval0`, indexed by `(e, α)`.  Book context: Chapter 5
  of the SCT book.
  -/
  lf_opaque lift0Cat (E : SCat) (B : SCat) (p : Functor E B)
    (v : Obj (directedPullbackCat E B B p (idFunctor B))) : SCat
  /-- Category of contravariant lifts for `directedEval1`, indexed by `(α, e')`.  Book context:
  Chapter 5 of the SCT book.
  -/
  lf_opaque lift1Cat (E : SCat) (B : SCat) (p : Functor E B)
    (v : Obj (directedPullbackCat B E B (idFunctor B) p)) : SCat
  /-- Adjunction data between two functors; Chapter 5. -/
  syntax_sort Adjunction (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C) : Type u

extend_type_theory SCT where

  model_section Chapter5

  /-- Source fibration has its canonical cartesian structure; Chapter 5 structure data. -/
  lf_opaque sourceCartesian (C : SCat) :
    CartesianFibrationWitness (funCat intervalCat C) C (sourceFunctor C) (sourceFibration C)
  /-- Target fibration has its canonical cocartesian structure; Chapter 5 structure data. -/
  lf_opaque targetCocartesian (C : SCat) :
    CocartesianFibrationWitness (funCat intervalCat C) C (targetFunctor C)
      (targetFibration C)
  /-- Pullback/base-change fibration; Chapter 5 stability data. -/
  lf_opaque baseChangeFibration (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (B' : SCat) (q : Functor B' B) :
    Fibration (pullbackCat B' E B q p) B' (pullbackPr1 B' E B q p)
  /-- Cartesian structure is stable under base change; Chapter 5 stability data. -/
  lf_opaque baseChangeCartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (B' : SCat) (q : Functor B' B) :
    CartesianFibrationWitness (pullbackCat B' E B q p) B' (pullbackPr1 B' E B q p)
      (baseChangeFibration E B p fib B' q)
  /-- Cocartesian structure is stable under base change; Chapter 5 stability data. -/
  lf_opaque baseChangeCocartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (B' : SCat) (q : Functor B' B) :
    CocartesianFibrationWitness (pullbackCat B' E B q p) B'
      (pullbackPr1 B' E B q p) (baseChangeFibration E B p fib B' q)

extend_type_theory SCT where

  model_section Chapter5

  /-- Unit natural transformation of an adjunction.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque adjunctionUnit (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C)
    (adj : Adjunction C D L R) : NatTrans C C (idFunctor C) (compFunctor C D C L R)
  /-- Counit natural transformation of an adjunction.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque adjunctionCounit (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C)
    (adj : Adjunction C D L R) : NatTrans D D (compFunctor D C D R L) (idFunctor D)
  /-- Cocartesian structure supplies a left adjoint section of `directedEval0`.  Book context:
  Chapter 5 of the SCT book.
  -/
  lf_def cocartesianLiftSection : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (fib : Fibration E B p) ⇒ (cocart : CocartesianFibrationWitness E B p fib) ⇒
      LeftAdjointSection (funCat intervalCat E)
        (directedPullbackCat E B B p (idFunctor B)) (directedEval0 E B p) :=
    fun E B p fib cocart => cocart
  /-- Cartesian structure supplies a right adjoint section of `directedEval1`.  Book context:
  Chapter 5 of the SCT book.
  -/
  lf_def cartesianLiftSection : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (fib : Fibration E B p) ⇒ (cart : CartesianFibrationWitness E B p fib) ⇒
      RightAdjointSection (funCat intervalCat E)
        (directedPullbackCat B E B (idFunctor B) p) (directedEval1 E B p) :=
    fun E B p fib cart => cart
  /-- Cocartesian morphism evidence for a morphism in the total category.
  Book context:Chapter 5 of
  the SCT book.
  -/
  syntax_sort CocartesianMorphism (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (u : Functor intervalCat E) : Type u

extend_type_theory SCT where

  model_section Chapter5

  /-- Every left fibration is cocartesian; projection data for the Chapter 5 left-fibration
  package. -/
  lf_opaque leftFibrationCocartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (left : LeftFibrationWitness E B p fib) :
    CocartesianFibrationWitness E B p fib
  /-- Every right fibration is cartesian; projection data for the Chapter 5 right-fibration
  package. -/
  lf_opaque rightFibrationCartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (right : RightFibrationWitness E B p fib) :
    CartesianFibrationWitness E B p fib

extend_type_theory SCT where

  model_section Chapter5

  /-- Cartesian morphism evidence for a morphism in the total category.  Book context: Chapter 5 of
  the SCT book.
  -/
  syntax_sort CartesianMorphism (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (u : Functor intervalCat E) : Type u
  /-- Cocartesian functor between cocartesian fibrations; Chapter 5. -/
  syntax_sort CocartesianFunctorWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E') : Type u
  /-- Locally cocartesian fibration structure; Chapter 5. -/
  syntax_sort LocallyCocartesianFibrationWitness (E : SCat) (B : SCat)
    (p : Functor E B) (fib : Fibration E B p) : Type u
  /-- Locally cartesian fibration structure; Chapter 5. -/
  syntax_sort LocallyCartesianFibrationWitness (E : SCat) (B : SCat)
    (p : Functor E B) (fib : Fibration E B p) : Type u
  /-- Cartesian functor between cartesian fibrations; Chapter 5 dual to cocartesian functors. -/
  syntax_sort CartesianFunctorWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cart' : CartesianFibrationWitness E' B p' fib') (F : Functor E E') : Type u

  /-- Fiberwise initial-object evidence; Axiom L. -/
  syntax_sort FiberwiseInitialWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) : Type u

extend_type_theory SCT where

  model_section Chapter5

  /-- Chosen cocartesian lift functor, the underlying functor of the left adjoint section supplied
  by cocartesian structure.  Book context: Chapter 5 of the SCT book.
  -/
  lf_def cocartesianLiftFunctor : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (fib : Fibration E B p) ⇒ CocartesianFibrationWitness E B p fib ⇒
      Functor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E) :=
    fun E B p fib cocart => leftAdjointSectionFunctor (funCat intervalCat E)
      (directedPullbackCat E B B p (idFunctor B)) (directedEval0 E B p) cocart

extend_type_theory SCT where

  model_section Chapter5

  /-- Map on directed pullbacks induced by a functor over the base; Chapter 5 transport data. -/
  lf_opaque directedPullbackMapOverBase (E : SCat) (B : SCat) (p : Functor E B)
    (E' : SCat) (p' : Functor E' B) (F : Functor E E') :
    Functor (directedPullbackCat E B B p (idFunctor B))
      (directedPullbackCat E' B B p' (idFunctor B))
  /-- Beck-Chevalley transformation associated to a functor over the base; Chapter 5 data. -/
  lf_opaque beckChevalleyTransformation (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E') :
    NatTrans (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E')
      (compFunctor (directedPullbackCat E B B p (idFunctor B))
        (directedPullbackCat E' B B p' (idFunctor B)) (funCat intervalCat E')
        (directedPullbackMapOverBase E B p E' p' F)
        (cocartesianLiftFunctor E' B p' fib' cocart'))
      (compFunctor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E)
        (funCat intervalCat E') (cocartesianLiftFunctor E B p fib cocart)
        (postcompFunctor intervalCat E E' F))
  /-- Cocartesian functor witnesses make the Beck-Chevalley transformation invertible. -/
  lf_opaque cocartesianFunctorBeckChevalley (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E')
    (hF : CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F) :
    NatIso (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E')
      (compFunctor (directedPullbackCat E B B p (idFunctor B))
        (directedPullbackCat E' B B p' (idFunctor B)) (funCat intervalCat E')
        (directedPullbackMapOverBase E B p E' p' F)
        (cocartesianLiftFunctor E' B p' fib' cocart'))
      (compFunctor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E)
        (funCat intervalCat E') (cocartesianLiftFunctor E B p fib cocart)
        (postcompFunctor intervalCat E E' F))
  /-- Identity cocartesian functor; Chapter 5 closure data. -/
  lf_opaque idCocartesianFunctor (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    CocartesianFunctorWitness E B p fib cocart E p fib cocart (idFunctor E)
  /-- Composition of cocartesian functors; Chapter 5 closure data. -/
  lf_opaque compCocartesianFunctor (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E')
    (hF : CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F)
    (E'' : SCat) (p'' : Functor E'' B) (fib'' : Fibration E'' B p'')
    (cocart'' : CocartesianFibrationWitness E'' B p'' fib'') (G : Functor E' E'')
    (hG : CocartesianFunctorWitness E' B p' fib' cocart' E'' p'' fib'' cocart'' G) :
    CocartesianFunctorWitness E B p fib cocart E'' p'' fib'' cocart''
      (compFunctor E E' E'' F G)

extend_type_theory SCT where

  model_section Chapter5

  /-- Fiberwise terminal-object evidence; Axiom L. -/
  syntax_sort FiberwiseTerminalWitness (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) : Type u
  /-- Cartesian plus fiberwise initial data assembles a left adjoint section; Axiom L. -/
  lf_opaque universal_left_adjoint_section (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (init : FiberwiseInitialWitness E B p fib) : Functor B E
  /-- The left adjoint section lies over the base; Axiom L. -/
  lf_opaque universalLeftSectionBase (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (init : FiberwiseInitialWitness E B p fib) :
    NatIso B B
      (compFunctor B E B (universal_left_adjoint_section E B p fib cart init) p)
      (idFunctor B)
  /-- Cocartesian plus fiberwise terminal data assembles a right adjoint section; Axiom L. -/
  lf_opaque universal_right_adjoint_section (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (term : FiberwiseTerminalWitness E B p fib) : Functor B E
  /-- The right adjoint section lies over the base; Axiom L. -/
  lf_opaque universalRightSectionBase (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (term : FiberwiseTerminalWitness E B p fib) :
    NatIso B B
      (compFunctor B E B (universal_right_adjoint_section E B p fib cocart term) p)
      (idFunctor B)
  /-- Contextual fibration indexed by a contextual functor.
  Book context:Chapter 5 of the SCT book.
  -/
  syntax_sort ContextFibration (Γ : SCat) (E : ContextCat Γ) (B : ContextCat Γ)
    (p : ContextFunctor Γ E B) : Type u
  /-- Contextual cartesian fibration witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ContextCartesianFibrationWitness (Γ : SCat) (E : ContextCat Γ) (B : ContextCat Γ)
    (p : ContextFunctor Γ E B) (fib : ContextFibration Γ E B p) : Type u
  /-- Contextual cocartesian fibration witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ContextCocartesianFibrationWitness (Γ : SCat) (E : ContextCat Γ) (B : ContextCat Γ)
    (p : ContextFunctor Γ E B) (fib : ContextFibration Γ E B p) : Type u
  /-- Pullback-indexing shape `⌟ = {0,1} ★ *` for cospans.  Book context: Chapter 5 of the SCT book.
  -/
  lf_opaque pullbackShapeCat : SCat

extend_type_theory SCT where

  model_section Chapter5

  /-- Absolute fibrations weaken to contextual fibrations; Chapter 5 contextual-fibration data. -/
  lf_opaque weakenContextFibration (Γ : SCat) (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) :
    ContextFibration Γ (weakenContextCat Γ E) (weakenContextCat Γ B)
      (weakenContextFunctor Γ E B p)

extend_type_theory SCT where

  model_section Chapter5

  /-- Pushout-indexing shape `⌜ = * ★ {0,1}` for spans.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque pushoutShapeCat : SCat
  /-- A diagram of shape `J` in `C`.  Book context: Chapter 5 of the SCT book. -/
  syntax_abbrev Diagram (J : SCat) (C : SCat) := Functor J C
  /-- Cone category over a diagram.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque coneCat (J : SCat) (C : SCat) (D : Diagram J C) : SCat
  /-- Cocone category under a diagram.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque coconeCat (J : SCat) (C : SCat) (D : Diagram J C) : SCat
  /-- Limit-cone witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort LimitCone (J : SCat) (C : SCat) (D : Diagram J C) : Type u
  /-- Colimit-cocone witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ColimitCocone (J : SCat) (C : SCat) (D : Diagram J C) : Type u
  /-- `C` admits limits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort HasLimitsOfShape (J : SCat) (C : SCat) : Type u
  /-- `C` admits colimits of shape `J`.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort HasColimitsOfShape (J : SCat) (C : SCat) : Type u
  /-- Right adjoint limit functor to constant diagrams.  Book context: Chapter 5 of the SCT book. -/
  lf_opaque limitFunctor (J : SCat) (C : SCat) (h : HasLimitsOfShape J C) :
    Functor (funCat J C) C
  /-- Left adjoint colimit functor to constant diagrams.
  Book context:Chapter 5 of the SCT book. -/
  lf_opaque colimitFunctor (J : SCat) (C : SCat) (h : HasColimitsOfShape J C) :
    Functor (funCat J C) C

extend_type_theory SCT where

  model_section Chapter5

  /-- Absolute cocartesian fibrations are locally cocartesian in context; Chapter 5 structure data.
  -/
  lf_opaque locallyCocartesianOfCocartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    LocallyCocartesianFibrationWitness E B p fib
  /-- Absolute cartesian fibrations are locally cartesian in context; Chapter 5 structure data. -/
  lf_opaque locallyCartesianOfCartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib) :
    LocallyCartesianFibrationWitness E B p fib

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
  syntax_abbrev FullyFaithful (C : SCat) (D : SCat) (F : Functor C D) :=
    CatEquiv (funCat intervalCat C)
      (pullbackCat (prodCat C C) (funCat intervalCat D) (prodCat D D)
        (objectPairFunctor C D F) (arrowEndpointFunctor D))
  /-- Conservative functors, represented by the core-pullback criterion.  Book context: Chapter 6 of
  the SCT book.
  -/
  syntax_abbrev Conservative (C : SCat) (D : SCat) (F : Functor C D) :=
    PullbackSquare (coreCat C) C (coreCat D) D (coreIncl C) (coreFunctor C D F) F (coreIncl D)
  /-- Strongly-surjective functors; Chapter 6 Fundamental Theorem. -/
  syntax_sort StronglySurjective (C : SCat) (D : SCat) (F : Functor C D) : Type u

namespace SCT

/- Theorem-shaped declaration admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Fully faithful functors induce equivalences on object-hom categories; Definition 6.1.1.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: derive this fiberwise equivalence from the endpoint-pullback
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

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Fully faithful functors are conservative; Proposition 6.2.8.
  Book target: Proposition 6.2.8, fully faithful functors are conservative.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove using the arrow-map characterization and invertible morphisms.
  -/
  def fullyFaithfulConservative (C : SCat) (D : SCat) (F : Functor C D)
    (ff : FullyFaithful C D F) : Conservative C D F := sorry
  /-- Conservative functors reflect invertible morphisms.
  Book target: §6.2, conservative functors reflect invertible morphisms.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Unpack the conservative/core-pullback criterion. -/
  def conservativeReflectsIso (C : SCat) (D : SCat) (F : Functor C D)
    (cons : Conservative C D F) (f : Functor intervalCat C)
    (hf : InvertibleMorphism D (compFunctor intervalCat C D f F)) : InvertibleMorphism C f := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter6

  /-- Chosen preimage object for strong surjectivity; Definition 6.3.1. -/
  lf_opaque stronglySurjectivePreimage (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) (y : Obj D) : Obj C

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- A retraction makes a functor conservative.
  Book target: §6.2, retract arguments for conservativity.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove by composing the retraction data with the conservative
  criterion. -/
  def conservativeOfRetract (C : SCat) (D : SCat) (F : Functor C D)
    (R : Functor D C) (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) :
    Conservative C D F := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter6

  /-- Comparison from the chosen preimage to the target object; Definition 6.3.1. -/
  lf_opaque stronglySurjectiveBeta (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) (y : Obj D) :
    NatIso terminalCat D
      (compFunctor terminalCat C D (stronglySurjectivePreimage C D F surj y) F) y
  /-- Strong surjectivity as a section of the induced map on cores.  Book context: Chapter 6 of the
  SCT book.
  -/
  lf_opaque stronglySurjectiveSection (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) : Functor (coreCat D) (coreCat C)
  /-- The chosen section of `F^≃` is a section up to natural isomorphism.
  Book context:Chapter 6 of
  the SCT book.
  -/
  lf_opaque stronglySurjectiveSectionBeta (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) :
    NatIso (coreCat D) (coreCat D)
      (compFunctor (coreCat D) (coreCat C) (coreCat D)
        (stronglySurjectiveSection C D F surj) (coreFunctor C D F))
      (idFunctor (coreCat D))
  /-- Objectwise natural-isomorphism evidence for a natural transformation: each component is
  invertible.  Book target: Theorem 6.2.11. -/
  syntax_abbrev ObjectwiseNatIso (A : SCat) (C : SCat)
    (F : Functor A C) (G : Functor A C) (α : NatTrans A C F G) :=
    (x : Obj A) → InvertibleMorphism C (natTransComponent A C F G α x)
  /-- Componentwise invertibility of a natural isomorphism.  This is the source-facing direction of
  Theorem 6.2.11 until `NatIso` exposes its underlying componentwise data. -/
  lf_opaque natIsoObjectwiseComponent (A : SCat) (C : SCat)
    (F : Functor A C) (G : Functor A C) (α : NatIso A C F G) (x : Obj A) :
    InvertibleMorphism C
      (natTransComponent A C F G (natIsoToNatTrans A C F G α) x)
  /-- Natural isomorphisms give objectwise natural-isomorphism evidence. -/
  lf_def natIsoObjectwise :
      (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒ (G : Functor A C) ⇒
      (α : NatIso A C F G) ⇒ ObjectwiseNatIso A C F G (natIsoToNatTrans A C F G α) :=
    fun A C F G α x => natIsoObjectwiseComponent A C F G α x
  /-- Objectwise evidence says every component morphism is invertible. -/
  lf_def objectwiseNatIsoComponentInvertible :
      (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒ (G : Functor A C) ⇒
      (α : NatTrans A C F G) ⇒ ObjectwiseNatIso A C F G α ⇒
      (x : Obj A) ⇒ InvertibleMorphism C (natTransComponent A C F G α x) :=
    fun A C F G α h x => h x

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Fully faithful plus strongly surjective gives an equivalence; Chapter 6.
  Book target: Theorem 6.3.3, fully faithful plus strongly surjective implies equivalence.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Construct the inverse and unit/counit from strong-surjectivity data.
  -/
  def fundamental_theorem_equiv (C : SCat) (D : SCat) (F : Functor C D)
    (ff : FullyFaithful C D F) (surj : StronglySurjective C D F) : CatEquiv C D := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter6


  /-- CamelCase alias for the Fundamental Theorem.  Book context: Chapter 6 of the SCT book. -/
  lf_def fundamentalTheoremEquiv : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      FullyFaithful C D F ⇒ StronglySurjective C D F ⇒ CatEquiv C D :=
    fun C D F ff surj => fundamental_theorem_equiv C D F ff surj
  /-- Evidence that a functor over a base is an equivalence on each fiber.
  Book target: Theorem 6.4.9, the fiberwise criterion for equivalences of cocartesian fibrations.
  -/
  syntax_sort FiberwiseCatEquiv (E : SCat) (B : SCat) (p : Functor E B)
    (E' : SCat) (p' : Functor E' B) (F : Functor E E') : Type u
  syntax_sort_role FiberwiseCatEquiv : side_structure

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where



  /-- Objectwise evidence assembles a natural isomorphism; Theorem 6.2.11.
  Book target: Theorem 6.2.11, natural transformations are natural isomorphisms iff their components
  are invertible.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove using objectwise invertibility and the core of the functor
  category. -/
  def natIsoOfObjectwise (A : SCat) (C : SCat)
    (F : Functor A C) (G : Functor A C) (α : NatTrans A C F G)
    (h : ObjectwiseNatIso A C F G α) : NatIso A C F G := sorry
  /-- Equivalences are fully faithful; Chapter 6.
  Book target: §6.3, equivalences are fully faithful and strongly surjective.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Derive from the packaged equivalence data and the core map. -/
  def equivalenceFullyFaithful (C : SCat) (D : SCat) (e : CatEquiv C D) :
    FullyFaithful C D (catEquivForward C D e) := sorry
  /-- Equivalences are strongly surjective; Chapter 6.
  Book target: §6.3, equivalences are fully faithful and strongly surjective.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Derive from the packaged equivalence data and the core map. -/
  def equivalenceStronglySurjective (C : SCat) (D : SCat) (e : CatEquiv C D) :
    StronglySurjective C D (catEquivForward C D e) := sorry

end SCT

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- A full subcategory inclusion is an equivalence when it is strongly surjective on objects.
  Book target: Proposition 6.4.1/6.4.2, full subcategory inclusions that are strongly surjective are
  equivalences.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Combine full faithfulness of the inclusion with the Fundamental
  Theorem. -/
  def fullSubcategoryEquivOfStronglySurjective (C : SCat) (P : ObjectCollection C)
    (ss : StronglySurjective (fullSubcategory C P) C (fullSubcategoryIncl C P)) :
    CatEquiv (fullSubcategory C P) C := sorry
  /-- Fiberwise criterion for cocartesian functors to be equivalences.
  Book target: Theorem 6.4.9, fiberwise criterion for equivalences of cocartesian fibrations.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove by applying the Fundamental Theorem fiberwise and using
  cocartesian transport. -/
  def cocartesianFunctorFiberwiseEquiv (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E')
    (hF : CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F)
    (fiberwise : FiberwiseCatEquiv E B p E' p' F) : CatEquiv E E' := sorry
  /-- Fully faithful functors induce fully faithful functors on functor categories by
  postcomposition.
  Book target: §6.4, postcomposition with a fully faithful functor is fully faithful.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove from the objectwise/natural-isomorphism criterion. -/
  def funCatPostcompFullyFaithful (A : SCat) (C : SCat) (D : SCat)
    (F : Functor C D) (ff : FullyFaithful C D F) :
    FullyFaithful (funCat A C) (funCat A D) (postcompFunctor A C D F) := sorry



end SCT

/-- Chapter 7: universes and directed univalence; Axioms M and N. -/
extend_type_theory SCT where

  model_section Chapter7


  /-- Directed-univalence witness for a cocartesian fibration; Axiom N. -/
  syntax_sort DirectedUnivalenceWitness (U : SCat) (Udot : SCat) (p : Functor Udot U)
    (fib : Fibration Udot U p) (cocart : CocartesianFibrationWitness Udot U p fib) : Type u
  /-- Classifying transformations are source-shaped natural transformations between classifiers.
  Book context: Chapter 7 of the SCT book.
  -/
  syntax_abbrev ClassifyingTransformation (B : SCat) (U : SCat)
    (f : Functor B U) (g : Functor B U) := NatTrans B U f g
  /-- Universe-of-categories package; Axiom N and Definition 7.4.5. -/
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
  /-- Total category of the universe fibration; Axiom N. -/
  lf_opaque universeTotalCat (U : SCat) (u : UniverseWitness U) : SCat

extend_type_theory SCT where

  model_section Chapter7

  /-- Category of proof objects that a functor over `B` is cocartesian; Construction 7.1.2 data. -/
  lf_opaque isCocartesianFunctorCat (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p)
    (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q)
    (cocartq : CocartesianFibrationWitness F B q fibq) : SCat
  /-- Non-full subcategory `CoCart_B(E,F)` of cocartesian functors; Definition 7.1.10 data. -/
  lf_opaque cocartesianFunctorCat (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p)
    (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q)
    (cocartq : CocartesianFibrationWitness F B q fibq) : SCat
  /-- Inclusion `CoCart_B(E,F) → Fun_B(E,F)`; Definition 7.1.10 data. -/
  lf_opaque cocartesianFunctorCatIncl (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p) (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q) (cocartq : CocartesianFibrationWitness F B q fibq) :
    Functor (cocartesianFunctorCat B E F p fibp cocartp q fibq cocartq)
      (functorOverBaseCat B E F p q)
  /-- `CoCart_B(E,F)` is the subcategory selected by the Beck-Chevalley condition; Definition
  7.1.10 data. -/
  lf_opaque cocartesianFunctorCatSubcategory (B : SCat) (E : SCat) (F : SCat)
    (p : Functor E B) (fibp : Fibration E B p) (cocartp : CocartesianFibrationWitness E B p fibp)
    (q : Functor F B) (fibq : Fibration F B q) (cocartq : CocartesianFibrationWitness F B q fibq) :
    SubcategoryWitness (cocartesianFunctorCat B E F p fibp cocartp q fibq cocartq)
      (functorOverBaseCat B E F p q)
      (cocartesianFunctorCatIncl B E F p fibp cocartp q fibq cocartq)

extend_type_theory SCT where

  model_section Chapter7

  /-- Projection of the universe fibration; Axiom N. -/
  lf_opaque universeProjection (U : SCat) (u : UniverseWitness U) :
    Functor (universeTotalCat U u) U
  /-- Fibration structure on the universe projection; Axiom N. -/
  lf_opaque universeFibration (U : SCat) (u : UniverseWitness U) :
    Fibration (universeTotalCat U u) U (universeProjection U u)
  /-- Cocartesian structure on the universe projection; Axiom N. -/
  lf_opaque universeCocartesian (U : SCat) (u : UniverseWitness U) :
    CocartesianFibrationWitness (universeTotalCat U u) U (universeProjection U u)
      (universeFibration U u)
  /-- Directed univalence of the universe projection; Axiom N. -/
  lf_opaque universeDirectedUnivalence (U : SCat) (u : UniverseWitness U) :
    DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u)
  /-- Total category classified by a map into a universe; Axiom N. -/
  lf_def classifiedTotalCat : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ SCat :=
    fun U u B f => pullbackCat B (universeTotalCat U u) U f (universeProjection U u)
  /-- Projection of a classified fibration; Axiom N. -/
  lf_def classifiedProjection : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ Functor (classifiedTotalCat U u B f) B :=
    fun U u B f => pullbackPr1 B (universeTotalCat U u) U f (universeProjection U u)
  /-- Fibration classified by a universe map; Axiom N. -/
  lf_def classifiedFibration : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        Fibration (classifiedTotalCat U u B f) B (classifiedProjection U u B f) :=
    fun U u B f => baseChangeFibration (universeTotalCat U u) U
      (universeProjection U u) (universeFibration U u) B f
  /-- Cocartesian structure classified by a universe map; Axiom N. -/
  lf_def classifiedCocartesian : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        CocartesianFibrationWitness (classifiedTotalCat U u B f) B
          (classifiedProjection U u B f) (classifiedFibration U u B f) :=
    fun U u B f => baseChangeCocartesian (universeTotalCat U u) U
      (universeProjection U u) (universeFibration U u) (universeCocartesian U u) B f
  /-- Unstraightening total category for a classifying map; Section 7.7.  Book context: Chapter 7 of
  the SCT book.
  -/
  lf_def unstraighteningTotal : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ SCat :=
    fun U u B f => classifiedTotalCat U u B f
  /-- Unstraightening projection for a classifying map; Section 7.7.  Book context: Chapter 7 of the
  SCT book.
  -/
  lf_def unstraighteningProjection : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ Functor (unstraighteningTotal U u B f) B :=
    fun U u B f => classifiedProjection U u B f
  /-- Unstraightening fibration structure for a classifying map; Section 7.7.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def unstraighteningFibration : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        Fibration (unstraighteningTotal U u B f) B (unstraighteningProjection U u B f) :=
    fun U u B f => classifiedFibration U u B f
  /-- Unstraightening cocartesian structure for a classifying map; Section 7.7.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def unstraighteningCocartesian : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒
        CocartesianFibrationWitness (unstraighteningTotal U u B f) B
          (unstraighteningProjection U u B f) (unstraighteningFibration U u B f) :=
    fun U u B f => classifiedCocartesian U u B f

  /-- Inclusion of the zero slice `B → [1] × B`; Section 7.2.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def zeroBaseInclusion : (B : SCat) ⇒ Functor B (prodCat intervalCat B) :=
    fun B => prodPair B intervalCat B
      (compFunctor B terminalCat intervalCat (terminalProjection B) intervalZero)
      (idFunctor B)
  /-- Inclusion of the one slice `B → [1] × B`; Section 7.2.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def oneBaseInclusion : (B : SCat) ⇒ Functor B (prodCat intervalCat B) :=
    fun B => prodPair B intervalCat B
      (compFunctor B terminalCat intervalCat (terminalProjection B) intervalOne)
      (idFunctor B)
  /-- Source fiber of a fibration over `[1] × B`; Definition 7.2.3. -/
  lf_def straighteningSourceTotal : (B : SCat) ⇒ (E : SCat) ⇒
      Functor E (prodCat intervalCat B) ⇒ SCat :=
    fun B E p => pullbackCat B E (prodCat intervalCat B) (zeroBaseInclusion B) p
  /-- Target fiber of a fibration over `[1] × B`; Definition 7.2.3. -/
  lf_def straighteningTargetTotal : (B : SCat) ⇒ (E : SCat) ⇒
      Functor E (prodCat intervalCat B) ⇒ SCat :=
    fun B E p => pullbackCat B E (prodCat intervalCat B) (oneBaseInclusion B) p
  /-- Projection of the source fiber over `B`; Definition 7.2.3. -/
  lf_def straighteningSourceProjection : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒
        Functor (straighteningSourceTotal B E p) B :=
    fun B E p => pullbackPr1 B E (prodCat intervalCat B) (zeroBaseInclusion B) p
  /-- Projection of the target fiber over `B`; Definition 7.2.3. -/
  lf_def straighteningTargetProjection : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒
        Functor (straighteningTargetTotal B E p) B :=
    fun B E p => pullbackPr1 B E (prodCat intervalCat B) (oneBaseInclusion B) p
  /-- Source-fiber fibration, by base change; Definition 7.2.3. -/
  lf_def straighteningSourceFibration : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ Fibration E (prodCat intervalCat B) p ⇒
        Fibration (straighteningSourceTotal B E p) B
          (straighteningSourceProjection B E p) :=
    fun B E p fib => baseChangeFibration E (prodCat intervalCat B) p fib B
      (zeroBaseInclusion B)
  /-- Target-fiber fibration, by base change; Definition 7.2.3. -/
  lf_def straighteningTargetFibration : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ Fibration E (prodCat intervalCat B) p ⇒
        Fibration (straighteningTargetTotal B E p) B
          (straighteningTargetProjection B E p) :=
    fun B E p fib => baseChangeFibration E (prodCat intervalCat B) p fib B
      (oneBaseInclusion B)
  /-- Source-fiber cocartesian structure, by base change; Definition 7.2.3. -/
  lf_def straighteningSourceCocartesian : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ (fib : Fibration E (prodCat intervalCat B) p) ⇒
      CocartesianFibrationWitness E (prodCat intervalCat B) p fib ⇒
        CocartesianFibrationWitness (straighteningSourceTotal B E p) B
          (straighteningSourceProjection B E p) (straighteningSourceFibration B E p fib) :=
    fun B E p fib cocart => baseChangeCocartesian E (prodCat intervalCat B) p fib
      cocart B (zeroBaseInclusion B)
  /-- Target-fiber cocartesian structure, by base change; Definition 7.2.3. -/
  lf_def straighteningTargetCocartesian : (B : SCat) ⇒ (E : SCat) ⇒
      (p : Functor E (prodCat intervalCat B)) ⇒ (fib : Fibration E (prodCat intervalCat B) p) ⇒
      CocartesianFibrationWitness E (prodCat intervalCat B) p fib ⇒
        CocartesianFibrationWitness (straighteningTargetTotal B E p) B
          (straighteningTargetProjection B E p) (straighteningTargetFibration B E p fib) :=
    fun B E p fib cocart => baseChangeCocartesian E (prodCat intervalCat B) p fib
      cocart B (oneBaseInclusion B)
  /-- Cocartesian functor category between two classified fibrations.
  Book context:Chapter 7 of the
  SCT book.
  -/
  lf_def classifiedCocartesianFunctorCat : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor B U ⇒ Functor B U ⇒ SCat :=
    fun U u B f g => cocartesianFunctorCat B (classifiedTotalCat U u B f)
      (classifiedTotalCat U u B g) (classifiedProjection U u B f) (classifiedFibration U u B f)
      (classifiedCocartesian U u B f) (classifiedProjection U u B g)
      (classifiedFibration U u B g) (classifiedCocartesian U u B g)

extend_type_theory SCT where

  model_section Chapter7

  /-- Straightening over `[1]`; Construction 7.2.1 and Definition 7.2.3 data. -/
  lf_opaque straighteningFunctor (B : SCat) (E : SCat)
    (p : Functor E (prodCat intervalCat B))
    (fib : Fibration E (prodCat intervalCat B) p)
    (cocart : CocartesianFibrationWitness E (prodCat intervalCat B) p fib) :
    Functor (straighteningSourceTotal B E p) (straighteningTargetTotal B E p)
  /-- Straightening is a cocartesian functor over the base; Construction 7.2.1/Lemma 7.2.2 data.
  -/
  lf_opaque straighteningFunctorCocartesian (B : SCat) (E : SCat)
    (p : Functor E (prodCat intervalCat B))
    (fib : Fibration E (prodCat intervalCat B) p)
    (cocart : CocartesianFibrationWitness E (prodCat intervalCat B) p fib) :
    CocartesianFunctorWitness (straighteningSourceTotal B E p) B
      (straighteningSourceProjection B E p) (straighteningSourceFibration B E p fib)
      (straighteningSourceCocartesian B E p fib cocart) (straighteningTargetTotal B E p)
      (straighteningTargetProjection B E p) (straighteningTargetFibration B E p fib)
      (straighteningTargetCocartesian B E p fib cocart)
      (straighteningFunctor B E p fib cocart)

extend_type_theory SCT where

  model_section Chapter7

  /-- Inclusion of classified cocartesian functors into the ordinary functor category.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def classifiedCocartesianFunctorUnderlying : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
        Functor (classifiedCocartesianFunctorCat U u B f g)
          (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)) :=
    fun U u B f g => compFunctor (classifiedCocartesianFunctorCat U u B f g)
      (functorOverBaseCat B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedProjection U u B g))
      (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
      (cocartesianFunctorCatIncl B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedFibration U u B f)
        (classifiedCocartesian U u B f)
        (classifiedProjection U u B g) (classifiedFibration U u B g)
        (classifiedCocartesian U u B g))
      (functorOverBaseIncl B (classifiedTotalCat U u B f) (classifiedTotalCat U u B g)
        (classifiedProjection U u B f) (classifiedProjection U u B g))

extend_type_theory SCT where

  model_section Chapter7

  /-- Directed-univalence equivalence between classifying transformations and cocartesian functors;
  Axiom N/Definition 7.3.10 data. -/
  lf_opaque directedUnivalenceMappingEquiv (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U) :
    CatEquiv (natTransCat B U f g) (classifiedCocartesianFunctorCat U u B f g)

extend_type_theory SCT where

  model_section Chapter7

  /-- Object of the cocartesian-functor category produced from a classifying transformation.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def directedUnivalenceCocartesianObject : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
        (universeFibration U u) (universeCocartesian U u)) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
      ClassifyingTransformation B U f g ⇒ Obj (classifiedCocartesianFunctorCat U u B f g) :=
    fun U u du B f g α => compFunctor terminalCat (natTransCat B U f g)
      (classifiedCocartesianFunctorCat U u B f g) α
      (catEquivForward (natTransCat B U f g) (classifiedCocartesianFunctorCat U u B f g)
        (directedUnivalenceMappingEquiv U u du B f g))
  /-- Underlying functor produced from a classifying transformation; Axiom N. -/
  lf_def directedUnivalenceFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
        (universeFibration U u) (universeCocartesian U u)) ⇒
      (B : SCat) ⇒ (f : Functor B U) ⇒ (g : Functor B U) ⇒
      ClassifyingTransformation B U f g ⇒
        Functor (classifiedTotalCat U u B f) (classifiedTotalCat U u B g) :=
    fun U u du B f g α => functorFromObject (classifiedTotalCat U u B f)
      (classifiedTotalCat U u B g)
      (compFunctor terminalCat (classifiedCocartesianFunctorCat U u B f g)
        (funCat (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
        (directedUnivalenceCocartesianObject U u du B f g α)
        (classifiedCocartesianFunctorUnderlying U u B f g))

  /-- Smallness relative to a universe; Axiom N. -/
  syntax_sort SmallWitness (U : SCat) (C : SCat) : Type u

extend_type_theory SCT where

  model_section Chapter7

  /-- The functor produced by directed univalence is cocartesian; Axiom N/Definition 7.3.10 data. -/
  lf_opaque directedUnivalenceFunctorCocartesian (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U)
    (α : ClassifyingTransformation B U f g) :
    CocartesianFunctorWitness (classifiedTotalCat U u B f) B (classifiedProjection U u B f)
      (classifiedFibration U u B f) (classifiedCocartesian U u B f)
      (classifiedTotalCat U u B g) (classifiedProjection U u B g)
      (classifiedFibration U u B g) (classifiedCocartesian U u B g)
      (directedUnivalenceFunctor U u du B f g α)
  /-- Directed univalence sends cocartesian functors back to transformations; Axiom N/Definition
  7.3.10 data. -/
  lf_opaque directedUnivalenceToTransformation (U : SCat) (u : UniverseWitness U)
    (du : DirectedUnivalenceWitness U (universeTotalCat U u) (universeProjection U u)
      (universeFibration U u) (universeCocartesian U u))
    (B : SCat) (f : Functor B U) (g : Functor B U)
    (F : Functor (classifiedTotalCat U u B f) (classifiedTotalCat U u B g))
    (hF : CocartesianFunctorWitness (classifiedTotalCat U u B f) B
      (classifiedProjection U u B f) (classifiedFibration U u B f)
      (classifiedCocartesian U u B f) (classifiedTotalCat U u B g)
      (classifiedProjection U u B g) (classifiedFibration U u B g)
      (classifiedCocartesian U u B g) F) : ClassifyingTransformation B U f g

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
    (hC : SmallWitness U C) : SmallWitness U (subcategory C W)
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

extend_type_theory SCT where

  model_section Chapter7

  /-- The initial object of internal category theory in `Cat`; §7.5 source data. -/
  lf_opaque catInternalInitial : Obj categoryUniverse
  /-- Internal product operation in `Cat`; Lemma 7.5.5 source data. -/
  lf_opaque catInternalProduct :
      Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse
  /-- Internal coproduct operation in `Cat`; Lemma 7.5.5 source data. -/
  lf_opaque catInternalCoproduct :
      Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse
  /-- Internal pullback operation in `Cat`; §7.5 source data. -/
  lf_opaque catInternalPullback :
      Functor (funCat pullbackShapeCat categoryUniverse) categoryUniverse
  /-- Internal functor-category/exponential operation in `Cat`; §7.5/Remark 7.5.15 source data. -/
  lf_opaque catInternalFunctorCategory :
    Functor (prodCat categoryUniverse categoryUniverse) categoryUniverse

extend_type_theory SCT where

  model_section Chapter7

  /-- Regular subuniverse generated above a small subcategory; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseCat (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) : SCat
  /-- Universe witness for a regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseWitness (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) : UniverseWitness (regularSubuniverseCat U u S iS embS hS)
  /-- Inclusion of a regular subuniverse into the ambient universe; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseIncl (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) : Functor (regularSubuniverseCat U u S iS embS hS) U
  /-- The regular subuniverse is small in the ambient universe; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseSmall (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) : SmallWitness U (regularSubuniverseCat U u S iS embS hS)
  /-- The regular subuniverse is regular; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseRegular (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) :
    RegularUniverseWitness (regularSubuniverseCat U u S iS embS hS)
      (regularSubuniverseWitness U u S iS embS hS)
  /-- The seed subcategory maps into the regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseLift (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) : Functor S (regularSubuniverseCat U u S iS embS hS)
  /-- The seed inclusion factors through the regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniverseLiftBeta (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) :
    NatIso S U
      (compFunctor S (regularSubuniverseCat U u S iS embS hS) U
        (regularSubuniverseLift U u S iS embS hS)
        (regularSubuniverseIncl U u S iS embS hS))
      iS

extend_type_theory SCT where

  model_section Chapter7

  /-- Universe of groupoids inside the universe of categories; §7.6 source data. -/
  lf_opaque groupoidUniverse : SCat
  /-- Universe package for groupoids; §7.6 source data. -/
  lf_opaque groupoidUniverseWitness : UniverseWitness groupoidUniverse
  /-- Cores of small categories are small groupoids; §7.6 source data. -/
  lf_opaque coreSmall (C : SCat) (hC : SmallWitness categoryUniverse C) :
    SmallWitness groupoidUniverse (coreCat C)

extend_type_theory SCT where

  model_section Chapter7

  /-- Taking groupoid cores is classified by a map into `Grpd`.  Book context: Chapter 7 of the SCT
  book.
  -/
  lf_def coreClassifyingMap : (C : SCat) ⇒ SmallWitness categoryUniverse C ⇒
      Functor terminalCat groupoidUniverse :=
    fun C hC => smallClassifyingMap groupoidUniverse groupoidUniverseWitness
      (coreCat C) (coreSmall C hC)

extend_type_theory SCT where

  model_section Chapter7

  /-- Inclusion of the groupoid universe into `Cat`; §7.6 source data. -/
  lf_opaque groupoidUniverseIncl : Functor groupoidUniverse categoryUniverse
  /-- The groupoid universe inclusion is an embedding; §7.6 source data. -/
  lf_opaque groupoidUniverseEmbedding :
    Embedding groupoidUniverse categoryUniverse groupoidUniverseIncl
  /-- The groupoid universe is regular; §7.6 source data. -/
  lf_opaque groupoidUniverseRegular :
    RegularUniverseWitness groupoidUniverse groupoidUniverseWitness
  /-- The universal family over `Grpd` is a left fibration; §7.6 source data. -/
  lf_opaque groupoidUniverseLeftFibration :
    LeftFibrationWitness (universeTotalCat groupoidUniverse groupoidUniverseWitness)
      groupoidUniverse (universeProjection groupoidUniverse groupoidUniverseWitness)
      (universeFibration groupoidUniverse groupoidUniverseWitness)

extend_type_theory SCT where

  model_section Chapter7

  /-- Primitive anima are small in the groupoid universe; §7.6 source data. -/
  lf_opaque animaSmall (A : Anima) : SmallWitness groupoidUniverse (animaCat A)

extend_type_theory SCT where

  model_section Chapter7

  /-- Classifying object of a primitive anima in the groupoid universe; Section 7.6.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def animaClassifyingMap : Anima ⇒ Functor terminalCat groupoidUniverse :=
    fun A => smallClassifyingMap groupoidUniverse groupoidUniverseWitness
      (animaCat A) (animaSmall A)

extend_type_theory SCT where

  model_section Chapter7

  /-- Geometric realization of a small category is a small groupoid; §7.6 source data. -/
  lf_opaque geometricRealizationSmall (C : SCat) (hC : SmallWitness categoryUniverse C) :
    SmallWitness groupoidUniverse (geometricRealization C)
  /-- Fiberwise localization of a cocartesian fibration; §7.6 source data. -/
  lf_opaque fiberwiseLocalizationTotal (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) : SCat
  /-- Projection of the fiberwise localization; §7.6 source data. -/
  lf_opaque fiberwiseLocalizationProjection (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    Functor (fiberwiseLocalizationTotal E B p fib cocart) B
  /-- Fibration structure on the fiberwise localization; §7.6 source data. -/
  lf_opaque fiberwiseLocalizationFibration (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    Fibration (fiberwiseLocalizationTotal E B p fib cocart) B
      (fiberwiseLocalizationProjection E B p fib cocart)
  /-- Fiberwise localization remains cocartesian; §7.6 source data. -/
  lf_opaque fiberwiseLocalizationCocartesian (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    CocartesianFibrationWitness (fiberwiseLocalizationTotal E B p fib cocart) B
      (fiberwiseLocalizationProjection E B p fib cocart)
      (fiberwiseLocalizationFibration E B p fib cocart)

extend_type_theory SCT where

  model_section Chapter7

  /-- The groupoid-universe classifier recovers the underlying anima-category; Section 7.6.  Book
  context: Chapter 7 of the SCT book.
  -/
  lf_def animaClassifyingEquiv : (A : Anima) ⇒
      CatEquiv (animaCat A)
        (classifiedTotalCat groupoidUniverse groupoidUniverseWitness terminalCat
          (animaClassifyingMap A)) :=
    fun A => smallClassifyingEquiv groupoidUniverse groupoidUniverseWitness
      (animaCat A) (animaSmall A)

extend_type_theory SCT where

  model_section Chapter7

  /-- Category of small cocartesian fibrations over a base; Theorem 7.7.8 source data. -/
  lf_opaque cocartesianFibrationsOverCat (U : SCat) (u : UniverseWitness U) (B : SCat) :
    SCat
  /-- Straightening/unstraightening equivalence over an arbitrary base; Theorem 7.7.8 source data.
  -/
  lf_opaque straighteningUnstraighteningEquiv (U : SCat) (u : UniverseWitness U) (B : SCat) :
    CatEquiv (cocartesianFibrationsOverCat U u B) (funCat B U)

extend_type_theory SCT where

  model_section Chapter7

  /-- Straightening sends a small cocartesian fibration to its classifying functor.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def straighteningClassifyingFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor (cocartesianFibrationsOverCat U u B) (funCat B U) :=
    fun U u B => catEquivForward (cocartesianFibrationsOverCat U u B) (funCat B U)
      (straighteningUnstraighteningEquiv U u B)
  /-- Unstraightening sends a classifying functor to its pullback fibration.
  Book context:Chapter 7
  of the SCT book.
  -/
  lf_def unstraighteningClassifyingFunctor : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (B : SCat) ⇒ Functor (funCat B U) (cocartesianFibrationsOverCat U u B) :=
    fun U u B => catEquivBackward (cocartesianFibrationsOverCat U u B) (funCat B U)
      (straighteningUnstraighteningEquiv U u B)
  /-- Category of small left fibrations over a base, represented by cocartesian fibrations
  classified in `Grpd`.  Book context: Chapter 7 of the SCT book.
  -/
  lf_def leftFibrationsOverCat : (U : SCat) ⇒ UniverseWitness U ⇒ (B : SCat) ⇒ SCat :=
    fun U u B => cocartesianFibrationsOverCat U u B
  /-- Left fibrations over `B` are classified by maps into `Grpd`.  Book context: Chapter 7 of the
  SCT book.
  -/
  lf_def leftFibrationStraighteningEquiv : (B : SCat) ⇒
      CatEquiv (leftFibrationsOverCat groupoidUniverse groupoidUniverseWitness B)
        (funCat B groupoidUniverse) :=
    fun B => straighteningUnstraighteningEquiv groupoidUniverse groupoidUniverseWitness B
  /-- Constructive regularity closure data generated from a universe.
  Book context:Chapter 7 of the
  SCT book.
  -/
  syntax_sort ConstructiveRegularUniverseWitness (U : SCat) (u : UniverseWitness U) : Type u

extend_type_theory SCT where

  model_section Chapter7

  /-- Universal composable pair of small cocartesian fibrations; §7.8 source data. -/
  lf_opaque universalComposablePairCat (U : SCat) (u : UniverseWitness U) : SCat
  /-- Projection from the universal composable-pair category; §7.8 source data. -/
  lf_opaque universalComposablePairProjection (U : SCat) (u : UniverseWitness U) :
    Functor (universalComposablePairCat U u) U

extend_type_theory SCT where

  model_section Chapter7

  /-- The fixed universe classifies cocartesian fibrations; Axiom N. -/
  lf_opaque directed_univalence_classifies (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    SmallCocartesianFibrationWitness categoryUniverse E B p fib cocart

extend_type_theory SCT where

  model_section Chapter7

  /-- Constructive regularity implies regularity; §7.8 source data. -/
  lf_opaque regularOfConstructiveRegular (U : SCat) (u : UniverseWitness U)
    (h : ConstructiveRegularUniverseWitness U u) : RegularUniverseWitness U u
