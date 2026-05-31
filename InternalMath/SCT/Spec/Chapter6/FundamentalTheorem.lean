/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter6.Retracts

@[expose] public section

extend_type_theory SCT where

  model_section Chapter6

  /-- Strong surjectivity as a section of the induced map on cores; Definition 6.3.1. -/
  lf_def stronglySurjectiveSection : (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
      StronglySurjective C D F ⇒ Functor (coreCat D) (coreCat C) :=
    fun C D F surj => fst surj
  /-- The chosen section of `F^≃` is a section up to natural isomorphism; Definition 6.3.1. -/
  lf_def stronglySurjectiveSectionBeta : (C : SCat) ⇒ (D : SCat) ⇒
      (F : Functor C D) ⇒ (surj : StronglySurjective C D F) ⇒
        NatIso (coreCat D) (coreCat D)
          (compFunctor (coreCat D) (coreCat C) (coreCat D)
            (stronglySurjectiveSection C D F surj) (coreFunctor C D F))
          (idFunctor (coreCat D)) :=
    fun C D F surj => snd surj
  /-- Componentwise invertibility stored in objectwise natural-isomorphism evidence; the package
  form follows Theorem 6.2.11. -/
  lf_opaque objectwiseNatIsoComponent (A : SCat) (C : SCat)
    (F : Functor A C) (G : Functor A C) (α : NatTrans A C F G)
    (h : ObjectwiseNatIso A C F G α) (x : Obj A) :
    InvertibleMorphism C (natTransComponent A C F G α x)
  /-- Componentwise invertibility of a natural isomorphism, by projecting the public package. -/
  lf_def natIsoObjectwiseComponent :
      (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒ (G : Functor A C) ⇒
      (α : NatIso A C F G) ⇒ (x : Obj A) ⇒
      InvertibleMorphism C
        (natTransComponent A C F G (natIsoToNatTrans A C F G α) x) :=
    fun A C F G α x => objectwiseNatIsoComponent A C F G
      (natIsoToNatTrans A C F G α) (snd α) x
  /-- Natural isomorphisms give objectwise natural-isomorphism evidence. -/
  lf_def natIsoObjectwise :
      (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒ (G : Functor A C) ⇒
      (α : NatIso A C F G) ⇒ ObjectwiseNatIso A C F G (natIsoToNatTrans A C F G α) :=
    fun A C F G α => snd α
  /-- Objectwise evidence says every component morphism is invertible. -/
  lf_def objectwiseNatIsoComponentInvertible :
      (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒ (G : Functor A C) ⇒
      (α : NatTrans A C F G) ⇒ ObjectwiseNatIso A C F G α ⇒
      (x : Obj A) ⇒ InvertibleMorphism C (natTransComponent A C F G α x) :=
    fun A C F G α h x => objectwiseNatIsoComponent A C F G α h x

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
  /-- Objectwise evidence assembles a natural isomorphism; Theorem 6.2.11. -/
  lf_def natIsoOfObjectwise : (A : SCat) ⇒ (C : SCat) ⇒ (F : Functor A C) ⇒
      (G : Functor A C) ⇒ (α : NatTrans A C F G) ⇒ ObjectwiseNatIso A C F G α ⇒
      NatIso A C F G :=
    fun A C F G α h => ⟨α, h⟩
  /-- Evidence that the induced map on one fiber is an equivalence. -/
  syntax_abbrev FiberMapEquiv (E : SCat) (B : SCat) (p : Functor E B)
    (E' : SCat) (p' : Functor E' B) (F : Functor E E')
    (hBase : FunctorOverBase E B p E' p' F) (b : Obj B) :=
    Σ e : CatEquiv (fiberCat E B p b) (fiberCat E' B p' b),
      NatIso (fiberCat E B p b) (fiberCat E' B p' b)
        (catEquivForward (fiberCat E B p b) (fiberCat E' B p' b) e)
        (fiberMap E B p E' p' F hBase b)
  /-- Evidence that a functor over a base is an equivalence on each fiber.
  Book target: Theorem 6.4.7/6.4.9, the fiberwise criterion for equivalences of cocartesian
  fibrations. -/
  syntax_abbrev FiberwiseCatEquiv (E : SCat) (B : SCat) (p : Functor E B)
    (E' : SCat) (p' : Functor E' B) (F : Functor E E')
    (hBase : FunctorOverBase E B p E' p' F) :=
    (b : Obj B) → FiberMapEquiv E B p E' p' F hBase b
  /-- The equivalence on a specified fiber. -/
  lf_def fiberwiseCatEquivAt : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (F : Functor E E') ⇒
      (hBase : FunctorOverBase E B p E' p' F) ⇒
      FiberwiseCatEquiv E B p E' p' F hBase ⇒ (b : Obj B) ⇒
        CatEquiv (fiberCat E B p b) (fiberCat E' B p' b) :=
    fun E B p E' p' F hBase h b => fst (h b)
  /-- The chosen fiber equivalence has forward functor the induced fiber map. -/
  lf_def fiberwiseCatEquivForwardBeta :
      (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (F : Functor E E') ⇒
      (hBase : FunctorOverBase E B p E' p' F) ⇒
      (h : FiberwiseCatEquiv E B p E' p' F hBase) ⇒ (b : Obj B) ⇒
        NatIso (fiberCat E B p b) (fiberCat E' B p' b)
          (catEquivForward (fiberCat E B p b) (fiberCat E' B p' b)
            (fiberwiseCatEquivAt E B p E' p' F hBase h b))
          (fiberMap E B p E' p' F hBase b) :=
    fun E B p E' p' F hBase h b => snd (h b)

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where



  /-- Equivalences are fully faithful; Chapter 6.
  Book target: §6.3, equivalences are fully faithful and strongly surjective.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Derive from the packaged equivalence data and the core map. -/
  def equivalenceFullyFaithful (C : SCat) (D : SCat) (e : CatEquiv C D) :
    FullyFaithful C D (catEquivForward C D e) := sorry
  /-- Equivalences are strongly surjective; Chapter 6.
  Book target: §6.3, equivalences are strongly surjective.
  Status: temporary sorry-admitted structural theorem package; not a model field. -/
  def equivalenceStronglySurjective (C : SCat) (D : SCat) (e : CatEquiv C D) :
    StronglySurjective C D (catEquivForward C D e) := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter6

  /-- Section on cores induced by an equivalence. -/
  lf_def equivalenceStronglySurjectiveSection : (C : SCat) ⇒ (D : SCat) ⇒
      (e : CatEquiv C D) ⇒ Functor (coreCat D) (coreCat C) :=
    fun C D e => stronglySurjectiveSection C D (catEquivForward C D e)
      (equivalenceStronglySurjective C D e)
  /-- Section-on-cores comparison induced by an equivalence. -/
  lf_def equivalenceStronglySurjectiveSectionBeta : (C : SCat) ⇒ (D : SCat) ⇒
      (e : CatEquiv C D) ⇒
        NatIso (coreCat D) (coreCat D)
          (compFunctor (coreCat D) (coreCat C) (coreCat D)
            (equivalenceStronglySurjectiveSection C D e)
            (coreFunctor C D (catEquivForward C D e)))
          (idFunctor (coreCat D)) :=
    fun C D e => stronglySurjectiveSectionBeta C D (catEquivForward C D e)
      (equivalenceStronglySurjective C D e)

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
    (fiberwise : FiberwiseCatEquiv E B p E' p' F
      (cocartesianFunctorOverBase E B p fib cocart E' p' fib' cocart' F hF)) : CatEquiv E E' :=
    sorry
  /-- Fully faithful functors induce fully faithful functors on functor categories by
  postcomposition.
  Book target: §6.4, postcomposition with a fully faithful functor is fully faithful.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To make this book-faithful: Prove from the objectwise/natural-isomorphism criterion. -/
  def funCatPostcompFullyFaithful (A : SCat) (C : SCat) (D : SCat)
    (F : Functor C D) (ff : FullyFaithful C D F) :
    FullyFaithful (funCat A C) (funCat A D) (postcompFunctor A C D F) := sorry



end SCT
