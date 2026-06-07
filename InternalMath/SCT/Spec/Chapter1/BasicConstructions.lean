/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Prelude

/-!
# Chapter 1 basic constructions: Axiom B and interval shapes

This file adds the basic categorical constructors and low-dimensional shapes from Chapter 1.

Book guide, paraphrasing the May 2026 draft:

- Axiom A.1(3) says dependent sums of anima-indexed anima fibers are anima. This file packages the
  fiber evidence as `allFibersAnima` and registers `sigma_anima_indexed_is_anima`.
- Axiom A.2 treats terms of `C` in context `Γ` as functors `Γ ⟶ C`. See `Term`, `universalTerm`,
  `objectFunctor`, and `objectOfFunctor`.
- Axioms B.1 and B.2 give terminal and initial categories, with uniqueness data. B.2' adds strict
  initiality.
- Axioms B.3--B.5 give products, coproducts, pullbacks, and their β/η or componentwise natural
  isomorphism data.
- Axiom B.4' gives coproduct base change and disjointness.
- Axiom B.6 gives functor categories, pre/postcomposition, evaluation, currying, uncurrying, and
  the currying equivalence.
- Axiom C supplies `[1]`, its endpoints, source/target evaluation for interval-shaped arrows, and
  the basic `[2]` shape used later by the square and Segal axioms.

Key declarations below include `terminalProjection`, `initialCat`, `prodCat`, `coprodCat`,
`pullbackCat`, `funCat`, `intervalCat`, `sourceFunctor`, `targetFunctor`, `identityMorphism`,
`simplex2Cat`, and `squareCat`.
-/

@[expose] public section

extend_type_theory SCT where

  /-- Chapter 1: the language of naive category theory; Axioms A--F. -/
  model_section Chapter1

  /-- Isomorphisms between absolute objects.  Book context: Chapter 1 of the SCT book. -/
  syntax_abbrev ObjIso {C : SCat} (x : Obj C) (y : Obj C) := NatIso terminalCat C x y
  /-- Evidence that every fiber of an anima-indexed family is an anima: each fiber is presented as
  equivalent to the underlying category of a primitive anima.  Book context: Axiom A.1(3). -/
  syntax_abbrev allFibersAnima (Γ : Anima) (C : AnimaIndexedCat Γ) :=
    (x : Obj (animaCat Γ)) → Σ A : Anima, CatEquiv (animaIndexedFiber Γ C x) (animaCat A)
  /-- The primitive anima witnessing that a chosen fiber is an anima. -/
  lf_def allFibersAnimaFiberWitness : (Γ : Anima) ⇒ (C : AnimaIndexedCat Γ) ⇒
      allFibersAnima Γ C ⇒ (x : Obj (animaCat Γ)) ⇒ Anima :=
    fun Γ C h x => fst (h x)
  /-- The equivalence from a chosen fiber to its witnessing primitive anima. -/
  lf_def allFibersAnimaFiberEquiv : (Γ : Anima) ⇒ (C : AnimaIndexedCat Γ) ⇒
      (h : allFibersAnima Γ C) ⇒ (x : Obj (animaCat Γ)) ⇒
      CatEquiv (animaIndexedFiber Γ C x) (animaCat (allFibersAnimaFiberWitness Γ C h x)) :=
    fun Γ C h x => snd (h x)
  /-- An anima-indexed sum of anima fibers is an anima; Axiom A.1(3). -/
  rule sigma_anima_indexed_is_anima (Γ : Anima) (C : AnimaIndexedCat Γ)
    (h : allFibersAnima Γ C) where
    conclusion : isAnimaCat (sigmaAnimaIndexed Γ C)
  /-- Pairing constructor for terms of an anima-indexed dependent sum.  Book context: Chapter 1 of
  the SCT book.
  -/
  lf_opaque sigmaAnimaIndexedPair (Γ : Anima) (C : AnimaIndexedCat Γ)
    (x : Obj (animaCat Γ)) (c : Obj (animaIndexedFiber Γ C x)) :
    Obj (sigmaAnimaIndexed Γ C)
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
  syntax_abbrev ContractionAt {C : SCat} (x : Obj C) :=
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
  /-- Projection from a fiber to the terminal object selecting the basepoint. -/
  lf_def fiberPointProjection : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      (y : Obj D) ⇒ Functor (fiberCat C D F y) terminalCat :=
    fun C D F y => pullbackPr2 C terminalCat D F y
  /-- Evidence that a functor between total categories lies over a fixed base. -/
  syntax_abbrev FunctorOverBase {E : SCat} {B : SCat} (p : Functor E B)
    {E' : SCat} (p' : Functor E' B) (F : Functor E E') :=
    NatIso E B (compFunctor E E' B F p') p
  /-- Compatibility isomorphism used to map fibers along a functor over the base. -/
  lf_def fiberMapCompat : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (F : Functor E E') ⇒
      FunctorOverBase E B p E' p' F ⇒ (b : Obj B) ⇒
        NatIso (fiberCat E B p b) B
          (compFunctor (fiberCat E B p b) E' B
            (compFunctor (fiberCat E B p b) E E' (fiberProjection E B p b) F) p')
          (compFunctor (fiberCat E B p b) terminalCat B (fiberPointProjection E B p b) b) :=
    fun E B p E' p' F hBase b =>
      compNatIso (fiberCat E B p b) B
        (compFunctor (fiberCat E B p b) E' B
          (compFunctor (fiberCat E B p b) E E' (fiberProjection E B p b) F) p')
        (compFunctor (fiberCat E B p b) E B (fiberProjection E B p b)
          (compFunctor E E' B F p'))
        (compFunctor (fiberCat E B p b) terminalCat B (fiberPointProjection E B p b) b)
        (assocFunctor (fiberCat E B p b) E E' B (fiberProjection E B p b) F p')
        (compNatIso (fiberCat E B p b) B
          (compFunctor (fiberCat E B p b) E B (fiberProjection E B p b)
            (compFunctor E E' B F p'))
          (compFunctor (fiberCat E B p b) E B (fiberProjection E B p b) p)
          (compFunctor (fiberCat E B p b) terminalCat B (fiberPointProjection E B p b) b)
          (preWhiskerNatIso (fiberCat E B p b) E B (fiberProjection E B p b)
            (compFunctor E E' B F p') p hBase)
          (pullbackComm E terminalCat B p b))
  /-- Induced map on fibers for a functor over a fixed base. -/
  lf_def fiberMap : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (F : Functor E E') ⇒
      FunctorOverBase E B p E' p' F ⇒ (b : Obj B) ⇒
        Functor (fiberCat E B p b) (fiberCat E' B p' b) :=
    fun E B p E' p' F hBase b =>
      pullbackLift (fiberCat E B p b) E' terminalCat B p' b
        (compFunctor (fiberCat E B p b) E E' (fiberProjection E B p b) F)
        (fiberPointProjection E B p b) (fiberMapCompat E B p E' p' F hBase b)
  /-- A pullback-square predicate for theorem statements, represented by the comparison to the
  pullback object.  Book context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev PullbackSquare {A : SCat} {B : SCat} {C : SCat} {D : SCat}
    (top : Functor A B) (left : Functor A C) (right : Functor B D) (bottom : Functor C D) :=
    CatEquiv A (pullbackCat B C D right bottom)
  /-- Embedding evidence for a functor, represented by equivalence with the self-pullback.  Book
  context: Chapter 1 of the SCT book.
  -/
  syntax_abbrev Embedding {C : SCat} {D : SCat} (F : Functor C D) :=
    CatEquiv C (pullbackCat C C D F F)
  /-- Self-pullback of the identity functor. -/
  lf_def identitySelfPullback : SCat ⇒ SCat :=
    fun C => pullbackCat C C C (idFunctor C) (idFunctor C)
  /-- First projection from the identity self-pullback. -/
  lf_def identitySelfPullbackPr1 : (C : SCat) ⇒ Functor (identitySelfPullback C) C :=
    fun C => pullbackPr1 C C C (idFunctor C) (idFunctor C)
  /-- Second projection from the identity self-pullback. -/
  lf_def identitySelfPullbackPr2 : (C : SCat) ⇒ Functor (identitySelfPullback C) C :=
    fun C => pullbackPr2 C C C (idFunctor C) (idFunctor C)
  /-- Diagonal comparison into the self-pullback of the identity functor. -/
  lf_def identitySelfPullbackDiagonal : (C : SCat) ⇒
      Functor C (identitySelfPullback C) :=
    fun C => pullbackLift C C C C (idFunctor C) (idFunctor C) (idFunctor C)
      (idFunctor C) (idNatIso C C (compFunctor C C C (idFunctor C) (idFunctor C)))
  /-- First projection β comparison for the identity diagonal. -/
  lf_def identityEmbeddingUnit : (C : SCat) ⇒
      NatIso C C
        (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
          (identitySelfPullbackPr1 C))
        (idFunctor C) :=
    fun C => pullbackBeta1 C C C C (idFunctor C) (idFunctor C) (idFunctor C)
      (idFunctor C) (idNatIso C C (compFunctor C C C (idFunctor C) (idFunctor C)))
  /-- Second projection β comparison for the identity diagonal. -/
  lf_def identityEmbeddingUnitPr2 : (C : SCat) ⇒
      NatIso C C
        (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
          (identitySelfPullbackPr2 C))
        (idFunctor C) :=
    fun C => pullbackBeta2 C C C C (idFunctor C) (idFunctor C) (idFunctor C)
      (idFunctor C) (idNatIso C C (compFunctor C C C (idFunctor C) (idFunctor C)))
  /-- First projection comparison used in the identity-embedding counit. -/
  lf_def identityEmbeddingCounitPr1 : (C : SCat) ⇒
      NatIso (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
            (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
          (identitySelfPullbackPr1 C))
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr1 C)) :=
    fun C => compNatIso (identitySelfPullback C) C
      (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
          (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
        (identitySelfPullbackPr1 C))
      (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
        (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
          (identitySelfPullbackPr1 C)))
      (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
        (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr1 C))
      (assocFunctor (identitySelfPullback C) C (identitySelfPullback C) C
        (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C)
        (identitySelfPullbackPr1 C))
      (compNatIso (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
            (identitySelfPullbackPr1 C)))
        (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (idFunctor C))
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr1 C))
        (preWhiskerNatIso (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
            (identitySelfPullbackPr1 C))
          (idFunctor C) (identityEmbeddingUnit C))
        (compNatIso (identitySelfPullback C) C
          (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
            (idFunctor C))
          (identitySelfPullbackPr1 C)
          (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
            (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr1 C))
          (rightUnitor (identitySelfPullback C) C (identitySelfPullbackPr1 C))
          (invNatIso (identitySelfPullback C) C
            (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
              (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr1 C))
            (identitySelfPullbackPr1 C)
            (leftUnitor (identitySelfPullback C) C (identitySelfPullbackPr1 C)))))
  /-- Second projection comparison used in the identity-embedding counit. -/
  lf_def identityEmbeddingCounitPr2 : (C : SCat) ⇒
      NatIso (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
            (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
          (identitySelfPullbackPr2 C))
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C)) :=
    fun C => compNatIso (identitySelfPullback C) C
      (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
          (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
        (identitySelfPullbackPr2 C))
      (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
        (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
          (identitySelfPullbackPr2 C)))
      (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
        (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C))
      (assocFunctor (identitySelfPullback C) C (identitySelfPullback C) C
        (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C)
        (identitySelfPullbackPr2 C))
      (compNatIso (identitySelfPullback C) C
        (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
            (identitySelfPullbackPr2 C)))
        (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (idFunctor C))
        (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
          (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C))
        (preWhiskerNatIso (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
          (compFunctor C (identitySelfPullback C) C (identitySelfPullbackDiagonal C)
            (identitySelfPullbackPr2 C))
          (idFunctor C) (identityEmbeddingUnitPr2 C))
        (compNatIso (identitySelfPullback C) C
          (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr1 C)
            (idFunctor C))
          (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr2 C)
            (idFunctor C))
          (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
            (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C))
          (pullbackComm C C C (idFunctor C) (idFunctor C))
          (compNatIso (identitySelfPullback C) C
            (compFunctor (identitySelfPullback C) C C (identitySelfPullbackPr2 C)
              (idFunctor C))
            (identitySelfPullbackPr2 C)
            (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
              (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C))
            (rightUnitor (identitySelfPullback C) C (identitySelfPullbackPr2 C))
            (invNatIso (identitySelfPullback C) C
              (compFunctor (identitySelfPullback C) (identitySelfPullback C) C
                (idFunctor (identitySelfPullback C)) (identitySelfPullbackPr2 C))
              (identitySelfPullbackPr2 C)
              (leftUnitor (identitySelfPullback C) C (identitySelfPullbackPr2 C))))))
  /-- Counit comparison for the identity embedding equivalence. -/
  lf_def identityEmbeddingCounit : (C : SCat) ⇒
      NatIso (identitySelfPullback C) (identitySelfPullback C)
        (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
          (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
        (idFunctor (identitySelfPullback C)) :=
    fun C => pullbackUniq (identitySelfPullback C) C C C (idFunctor C) (idFunctor C)
      (compFunctor (identitySelfPullback C) C (identitySelfPullback C)
        (identitySelfPullbackPr1 C) (identitySelfPullbackDiagonal C))
      (idFunctor (identitySelfPullback C)) (identityEmbeddingCounitPr1 C)
      (identityEmbeddingCounitPr2 C)
  /-- The identity functor is an embedding. -/
  lf_def identityEmbedding : (C : SCat) ⇒ Embedding C C (idFunctor C) :=
    fun C => catEquivOfData C (identitySelfPullback C) (identitySelfPullbackDiagonal C)
      (identitySelfPullbackPr1 C) (identityEmbeddingUnit C) (identityEmbeddingCounit C)

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
  /-- Pushout-square witness: a commutative square plus its mapping-out universal property.  Book
  target: pushout squares used throughout Chapter 1, especially Proposition 1.3.3 and Axiom J.1. -/
  syntax_abbrev PushoutSquare {A : SCat} {B : SCat} {C : SCat} {D : SCat}
    (top : Functor A B) (left : Functor A C) (right : Functor B D) (bottom : Functor C D) :=
    Σ comm : NatIso A D (compFunctor A B D top right) (compFunctor A C D left bottom),
      (X : SCat) → CatEquiv (funCat D X)
        (pullbackCat (funCat B X) (funCat C X) (funCat A X)
          (precompFunctor A B X top) (precompFunctor A C X left))
  /-- Commutativity component of a pushout square. -/
  lf_def pushoutSquareComm : (A : SCat) ⇒ (B : SCat) ⇒ (C : SCat) ⇒ (D : SCat) ⇒
      (top : Functor A B) ⇒ (left : Functor A C) ⇒ (right : Functor B D) ⇒
      (bottom : Functor C D) ⇒ PushoutSquare A B C D top left right bottom ⇒
      NatIso A D (compFunctor A B D top right) (compFunctor A C D left bottom) :=
    fun A B C D top left right bottom sq => fst sq
  /-- Mapping-out universal property associated to a pushout-square witness. -/
  lf_def pushoutSquareMappingEquiv : (A : SCat) ⇒ (B : SCat) ⇒ (C : SCat) ⇒
      (D : SCat) ⇒ (top : Functor A B) ⇒ (left : Functor A C) ⇒
      (right : Functor B D) ⇒ (bottom : Functor C D) ⇒
      PushoutSquare A B C D top left right bottom ⇒ (X : SCat) ⇒
      CatEquiv (funCat D X)
        (pullbackCat (funCat B X) (funCat C X) (funCat A X)
          (precompFunctor A B X top) (precompFunctor A C X left)) :=
    fun A B C D top left right bottom sq X => snd sq X
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
  syntax_abbrev InitialObjectWitness {C : SCat} (x : Obj C) :=
    (y : Obj C) → CatEquiv (objectHomCat C x y) terminalCat
  /-- Terminal-object witness for an object of a synthetic category.
  Book target: the terminal-object characterization used in §1.2 and later in §5.5. -/
  syntax_abbrev TerminalObjectWitness {C : SCat} (x : Obj C) :=
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
