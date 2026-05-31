/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter1.CellsAndSegal

@[expose] public section

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

  /-- Universal package for the core inclusion; Axiom G.  It stores the embedding of
  the core into the ambient category together with the lift, β comparison, and uniqueness for
  anima-indexed objects. -/
  lf_opaque coreUniversalPackage (C : SCat) :
    Σ emb : Embedding (coreCat C) C (coreIncl C),
      (A : Anima) → (F : Functor (animaCat A) C) →
        Σ K : Functor (animaCat A) (coreCat C),
          Σ β : NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C K
            (coreIncl C)) F,
            (L : Functor (animaCat A) (coreCat C)) →
              NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C L
                (coreIncl C)) F → NatIso (animaCat A) (coreCat C) L K
  /-- The core inclusion is an embedding; projection from the Axiom G core package. -/
  lf_def coreInclEmbedding : (C : SCat) ⇒ Embedding (coreCat C) C (coreIncl C) :=
    fun C => fst (coreUniversalPackage C)

extend_type_theory SCT where

  model_section Chapter2

  /-- Universal package for lifting anima-indexed objects through the groupoid core;
  Axiom G.  Projection from `coreUniversalPackage`. -/
  lf_def coreLiftPackage : (A : Anima) ⇒ (C : SCat) ⇒ (F : Functor (animaCat A) C) ⇒
      Σ K : Functor (animaCat A) (coreCat C),
        Σ β : NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C K
          (coreIncl C)) F,
          (L : Functor (animaCat A) (coreCat C)) →
            NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C L
              (coreIncl C)) F → NatIso (animaCat A) (coreCat C) L K :=
    fun A C F => snd (coreUniversalPackage C) A F
  /-- Lift an anima-parametrized object through the groupoid core; Axiom G. -/
  lf_def coreLift : (A : Anima) ⇒ (C : SCat) ⇒ Functor (animaCat A) C ⇒
      Functor (animaCat A) (coreCat C) :=
    fun A C F => fst (coreLiftPackage A C F)

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

  /-- β comparison for the core lift; Axiom G. -/
  lf_def coreLiftBeta : (A : Anima) ⇒ (C : SCat) ⇒ (F : Functor (animaCat A) C) ⇒
      NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C
        (coreLift A C F) (coreIncl C)) F :=
    fun A C F => fst (snd (coreLiftPackage A C F))
  /-- Uniqueness of core lifts from anima-parametrized objects; Axiom G. -/
  lf_def coreLiftUniq : (A : Anima) ⇒ (C : SCat) ⇒ (F : Functor (animaCat A) C) ⇒
      (K : Functor (animaCat A) (coreCat C)) ⇒
      NatIso (animaCat A) C (compFunctor (animaCat A) (coreCat C) C K
        (coreIncl C)) F ⇒ NatIso (animaCat A) (coreCat C) K (coreLift A C F) :=
    fun A C F K β => snd (snd (coreLiftPackage A C F)) K β
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

  /-- Coherence package for lifting natural isomorphisms through the core inclusion;
  Axiom G specialized to groupoid sources. -/
  lf_opaque coreLiftNatIsoFromGroupoidCoherencePackage (G : SCat) (C : SCat)
    (gG : GroupoidWitness G) (L : Functor G (coreCat C)) (M : Functor G (coreCat C))
    (α : NatIso G C (compFunctor G (coreCat C) C L (coreIncl C))
      (compFunctor G (coreCat C) C M (coreIncl C))) :
    Σ β : NatIsoIso G C (compFunctor G (coreCat C) C L (coreIncl C))
      (compFunctor G (coreCat C) C M (coreIncl C))
      (postWhiskerNatIso G (coreCat C) C L M (coreIncl C)
        (coreLiftNatIsoFromGroupoid G C gG L M α)) α,
      (N : NatIso G (coreCat C) L M) →
        NatIsoIso G C (compFunctor G (coreCat C) C L (coreIncl C))
          (compFunctor G (coreCat C) C M (coreIncl C))
          (postWhiskerNatIso G (coreCat C) C L M (coreIncl C) N) α →
        NatIsoIso G (coreCat C) L M N (coreLiftNatIsoFromGroupoid G C gG L M α)
  /-- Higher compatibility of a lifted core natural isomorphism with the original one; projection
  from the core lifting coherence package. -/
  lf_def coreLiftNatIsoFromGroupoidBeta : (G : SCat) ⇒ (C : SCat) ⇒
      (gG : GroupoidWitness G) ⇒ (L : Functor G (coreCat C)) ⇒
      (M : Functor G (coreCat C)) ⇒
      (α : NatIso G C (compFunctor G (coreCat C) C L (coreIncl C))
        (compFunctor G (coreCat C) C M (coreIncl C))) ⇒
      NatIsoIso G C (compFunctor G (coreCat C) C L (coreIncl C))
        (compFunctor G (coreCat C) C M (coreIncl C))
        (postWhiskerNatIso G (coreCat C) C L M (coreIncl C)
          (coreLiftNatIsoFromGroupoid G C gG L M α)) α :=
    fun G C gG L M α => fst (coreLiftNatIsoFromGroupoidCoherencePackage G C gG L M α)

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

namespace SCT

/- Theorem-shaped Chapter 2 consequences are admitted temporarily while moved out of the model
interface. -/
internal_defs where
  /-- The mapping anima is the core of the functor category.
  Book target: Chapter 2, the mapping-anima/core comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence from the object/functor interpretation of
  `Map(C,D)` and the definition of the maximal subgroupoid of the functor category. -/
  def mapAnimaCoreEquiv (C : SCat) (D : SCat) :
    CatEquiv (animaCat (mapAnima C D)) (coreCat (funCat C D)) := sorry

end SCT

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

namespace SCT

internal_defs where
  /-- Functor categories into a groupoid are groupoids.
  Book target: Proposition 2.1.2(4).
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove the interval-characterization of groupoids for `D^C` from the
  interval-characterization for `D`. -/
  def funCatTargetGroupoid (C : SCat) (D : SCat) (gD : GroupoidWitness D) :
    GroupoidWitness (funCat C D) := sorry

end SCT

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

namespace SCT

internal_defs where
  /-- The core of `[1]` is equivalent to two points.
  Book target: Axiom G.1 endpoint computation.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the endpoint equivalence from the maximal subgroupoid of
  the walking arrow. -/
  def intervalCoreEndpointEquiv :
    CatEquiv (coprodCat terminalCat terminalCat) (coreCat intervalCat) := sorry

end SCT

namespace SCT

internal_defs where
  /-- Product of cores comparison.
  Book target: Chapter 2 finite-limit closure of cores/groupoids.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove that taking maximal subgroupoids preserves binary products. -/
  def coreProductEquiv (C : SCat) (D : SCat) :
    CatEquiv (coreCat (prodCat C D)) (prodCat (coreCat C) (coreCat D)) := sorry

  /-- Pullback of cores comparison.
  Book target: Chapter 2 finite-limit closure of cores/groupoids.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove that taking maximal subgroupoids preserves pullbacks. -/
  def corePullbackEquiv (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E) :
    CatEquiv (coreCat (pullbackCat C D E F G))
      (pullbackCat (coreCat C) (coreCat D) (coreCat E)
        (coreFunctor C E F) (coreFunctor D E G)) := sorry

end SCT

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

namespace SCT

internal_defs where
  /-- The core of `[2]` is equivalent to three points.
  Book target: Axiom G.1 endpoint computation.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the equivalence from the maximal subgroupoid of `[2]`. -/
  def simplex2CoreEndpointEquiv : CatEquiv threePointCat (coreCat simplex2Cat) := sorry

  /-- Coproducts of groupoids are groupoids.
  Book target: Chapter 2 closure of groupoids under finite colimits used in the interval
  endpoint computations.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the interval-characterization witness for the coproduct. -/
  def coprodGroupoid (C : SCat) (D : SCat)
    (gC : GroupoidWitness C) (gD : GroupoidWitness D) : GroupoidWitness (coprodCat C D) :=
    sorry

  /-- Pullbacks of groupoids are groupoids.
  Book target: Chapter 2 finite-limit closure of groupoids.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: construct the interval-characterization witness for the pullback. -/
  def pullbackGroupoid (C : SCat) (D : SCat) (E : SCat)
    (F : Functor C E) (G : Functor D E)
    (gC : GroupoidWitness C) (gD : GroupoidWitness D) (gE : GroupoidWitness E) :
    GroupoidWitness (pullbackCat C D E F G) := sorry

  /-- The initial category is a groupoid.
  Book target: Chapter 2 finite-colimit closure of groupoids.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove the interval-characterization witness for the empty category. -/
  def initialGroupoid : GroupoidWitness initialCat := sorry

end SCT
