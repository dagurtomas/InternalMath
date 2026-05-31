/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.Universes

@[expose] public section

extend_type_theory SCT where

  model_section Chapter7

  /-- Regular-subuniverse package generated above a small subcategory;
  Definition 7.4.5 (Cat8). -/
  lf_opaque regularSubuniversePackage (U : SCat) (u : UniverseWitness U)
    (S : SCat) (iS : Functor S U) (embS : Embedding S U iS)
    (hS : SmallWitness U S) :
    Σ V : SCat,
      Σ v : UniverseWitness V,
        Σ incl : Functor V U,
          Σ smallV : SmallWitness U V,
            Σ regularV : RegularUniverseWitness V v,
              Σ lift : Functor S V, NatIso S U (compFunctor S V U lift incl) iS
  /-- Regular subuniverse generated above a small subcategory; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseCat : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ Embedding S U iS ⇒ SmallWitness U S ⇒ SCat :=
    fun U u S iS embS hS => fst (regularSubuniversePackage U u S iS embS hS)
  /-- Universe witness for a regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseWitness : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒ UniverseWitness (regularSubuniverseCat U u S iS embS hS) :=
    fun U u S iS embS hS => fst (snd (regularSubuniversePackage U u S iS embS hS))
  /-- Inclusion of a regular subuniverse into the ambient universe; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseIncl : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒ Functor (regularSubuniverseCat U u S iS embS hS) U :=
    fun U u S iS embS hS =>
      fst (snd (snd (regularSubuniversePackage U u S iS embS hS)))
  /-- The regular subuniverse is small in the ambient universe; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseSmall : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒ SmallWitness U (regularSubuniverseCat U u S iS embS hS) :=
    fun U u S iS embS hS =>
      fst (snd (snd (snd (regularSubuniversePackage U u S iS embS hS))))
  /-- The regular subuniverse is regular; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseRegular : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒
      RegularUniverseWitness (regularSubuniverseCat U u S iS embS hS)
        (regularSubuniverseWitness U u S iS embS hS) :=
    fun U u S iS embS hS =>
      fst (snd (snd (snd (snd (regularSubuniversePackage U u S iS embS hS)))))
  /-- The seed subcategory maps into the regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseLift : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒ Functor S (regularSubuniverseCat U u S iS embS hS) :=
    fun U u S iS embS hS =>
      fst (snd (snd (snd (snd (snd (regularSubuniversePackage U u S iS embS hS))))))
  /-- The seed inclusion factors through the regular subuniverse; Definition 7.4.5 (Cat8). -/
  lf_def regularSubuniverseLiftBeta : (U : SCat) ⇒ (u : UniverseWitness U) ⇒
      (S : SCat) ⇒ (iS : Functor S U) ⇒ (embS : Embedding S U iS) ⇒
      (hS : SmallWitness U S) ⇒
      NatIso S U
        (compFunctor S (regularSubuniverseCat U u S iS embS hS) U
          (regularSubuniverseLift U u S iS embS hS)
          (regularSubuniverseIncl U u S iS embS hS))
        iS :=
    fun U u S iS embS hS =>
      snd (snd (snd (snd (snd (snd (regularSubuniversePackage U u S iS embS hS))))))

extend_type_theory SCT where

  model_section Chapter7

  /-- Package for the universe of groupoids inside the universe of categories;
  §7.6. -/
  lf_opaque groupoidUniversePackage :
    Σ G : SCat,
      Σ g : UniverseWitness G,
        Σ coreData :
          ((C : SCat) → SmallWitness categoryUniverse C → SmallWitness G (coreCat C)),
          Σ incl : Functor G categoryUniverse,
            Σ emb : Embedding G categoryUniverse incl,
              Σ regular : RegularUniverseWitness G g,
                Σ leftFib : LeftFibrationWitness (universeTotalCat G g) G
                    (universeProjection G g) (universeFibration G g),
                  (A : Anima) → SmallWitness G (animaCat A)
  /-- Universe of groupoids inside the universe of categories; §7.6. -/
  lf_def groupoidUniverse : SCat := fst groupoidUniversePackage
  /-- Universe package for groupoids; §7.6. -/
  lf_def groupoidUniverseWitness : UniverseWitness groupoidUniverse :=
    fst (snd groupoidUniversePackage)
  /-- Cores of small categories are small groupoids; §7.6. -/
  lf_def coreSmall : (C : SCat) ⇒ SmallWitness categoryUniverse C ⇒
      SmallWitness groupoidUniverse (coreCat C) :=
    fun C hC => fst (snd (snd groupoidUniversePackage)) C hC
  /-- Inclusion of the groupoid universe into `Cat`; §7.6. -/
  lf_def groupoidUniverseIncl : Functor groupoidUniverse categoryUniverse :=
    fst (snd (snd (snd groupoidUniversePackage)))
  /-- The groupoid universe inclusion is an embedding; §7.6. -/
  lf_def groupoidUniverseEmbedding :
      Embedding groupoidUniverse categoryUniverse groupoidUniverseIncl :=
    fst (snd (snd (snd (snd groupoidUniversePackage))))
  /-- The groupoid universe is regular; §7.6. -/
  lf_def groupoidUniverseRegular :
      RegularUniverseWitness groupoidUniverse groupoidUniverseWitness :=
    fst (snd (snd (snd (snd (snd groupoidUniversePackage)))))
  /-- The universal family over `Grpd` is a left fibration; §7.6. -/
  lf_def groupoidUniverseLeftFibration :
      LeftFibrationWitness (universeTotalCat groupoidUniverse groupoidUniverseWitness)
        groupoidUniverse (universeProjection groupoidUniverse groupoidUniverseWitness)
        (universeFibration groupoidUniverse groupoidUniverseWitness) :=
    fst (snd (snd (snd (snd (snd (snd groupoidUniversePackage))))))
  /-- Primitive anima are small in the groupoid universe; §7.6. -/
  lf_def animaSmall : (A : Anima) ⇒ SmallWitness groupoidUniverse (animaCat A) :=
    fun A => snd (snd (snd (snd (snd (snd (snd groupoidUniversePackage)))))) A

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

  /-- Classifying object of a primitive anima in the groupoid universe; Section 7.6.  Book context:
  Chapter 7 of the SCT book.
  -/
  lf_def animaClassifyingMap : Anima ⇒ Functor terminalCat groupoidUniverse :=
    fun A => smallClassifyingMap groupoidUniverse groupoidUniverseWitness
      (animaCat A) (animaSmall A)
