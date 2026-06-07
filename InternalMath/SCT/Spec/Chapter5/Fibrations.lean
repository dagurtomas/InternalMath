/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter4.Contexts

/-!
# Chapter 5 fibration vocabulary and Axiom L

This file records the main fibration vocabulary from Chapter 5 and the functoriality of universal
objects.

Book guide, paraphrasing the May 2026 draft:

- `IsofibrationWitness` is the Chapter 5 isofibration condition; `Fibration` is its public
  abbreviation.
- `Adjunction`, `LeftAdjointSection`, and `RightAdjointSection` package the adjunction data used for
  initial and terminal objects in fibers.
- Directed or lax pullbacks are represented by `directedPullbackCat` and the associated projection
  and arrow data.
- Left/right/cartesian/cocartesian fibration witnesses are represented by
  `LeftFibrationWitness`, `RightFibrationWitness`, `CartesianFibrationWitness`, and
  `CocartesianFibrationWitness`.
- Source and target fibrations for arrow categories are `sourceFibration`, `targetFibration`,
  `sourceCartesian`, and `targetCocartesian`.
- Axiom L says universal objects vary functorially. The declarations include
  `fiberwiseInitialObject`, `fiberwiseTerminalObject`, `leftFibrationSectionFunctor`,
  `rightFibrationSectionFunctor`, and the base-compatibility fields.
- Locally cartesian/cocartesian fibrations and cocartesian functors are represented by
  `LocallyCartesianFibrationWitness`, `LocallyCocartesianFibrationWitness`,
  `CocartesianFunctorWitness`, `idCocartesianFunctor`, and `compCocartesianFunctor`.
-/

@[expose] public section

/-- Chapter 5: cartesian and cocartesian fibrations; Axiom L. -/
extend_type_theory SCT where

  model_section Chapter5


  /-- Isofibration witness for the base condition in Definition 5.6.1. -/
  syntax_sort IsofibrationWitness {E : SCat} {B : SCat} (p : Functor E B) : Type u
  /-- Chapter 5 fibration vocabulary is the book's isofibration condition. -/
  syntax_abbrev Fibration {E : SCat} {B : SCat} (p : Functor E B) := IsofibrationWitness E B p
  /-- Adjunction data between two functors; Chapter 5. -/
  syntax_def Adjunction (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C) : Type u :=
    sorry
  /-- A section of a functor that is left adjoint to it.
  Book context:Chapter 5 of the SCT book. -/
  syntax_def LeftAdjointSection (C : SCat) (D : SCat) (p : Functor C D) : Type u :=
    Σ s : Functor D C,
      Σ sec : NatIso (compFunctor s p) (idFunctor D), Adjunction D C s p
  /-- A section of a functor that is right adjoint to it.  Book context: Chapter 5 of the SCT book.
  -/
  syntax_def RightAdjointSection (C : SCat) (D : SCat) (p : Functor C D) : Type u :=
    Σ s : Functor D C,
      Σ sec : NatIso (compFunctor s p) (idFunctor D), Adjunction C D p s

namespace SCT

/- Projection API for the adjoint-section packages. -/
internal_defs where
  /-- Underlying section functor of a left-adjoint-section witness.  Book context: Chapter 5 of the
  SCT book.
  -/
  def leftAdjointSectionFunctor (C : SCat) (D : SCat) (p : Functor C D)
    (s : LeftAdjointSection C D p) : Functor D C := sorry
  /-- Underlying section functor of a right-adjoint-section witness.  Book context: Chapter 5 of the
  SCT book.
  -/
  def rightAdjointSectionFunctor (C : SCat) (D : SCat) (p : Functor C D)
    (s : RightAdjointSection C D p) : Functor D C := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter5

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
  syntax_abbrev CartesianFibrationWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) :=
    RightAdjointSection (funCat intervalCat E)
      (directedPullbackCat B E B (idFunctor B) p) (directedEval1 E B p)
  /-- Cocartesian structure on a fibration, represented by a left adjoint section of
  `directedEval0`. Book context: Chapter 5 of the SCT book.
  -/
  syntax_abbrev CocartesianFibrationWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) :=
    LeftAdjointSection (funCat intervalCat E)
      (directedPullbackCat E B B p (idFunctor B)) (directedEval0 E B p)
  /-- Left-fibration structure; Chapter 5. -/
  syntax_sort LeftFibrationWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) : Type u

extend_type_theory SCT where

  model_section Chapter5

  /-- Source fibration of a category; Chapter 5 source-fibration structure data from §5.8. -/
  lf_opaque sourceFibration (C : SCat) : Fibration (funCat intervalCat C) C (sourceFunctor C)
  /-- Target fibration of a category; Chapter 5 target-fibration structure data from §5.8. -/
  lf_opaque targetFibration (C : SCat) : Fibration (funCat intervalCat C) C (targetFunctor C)

extend_type_theory SCT where

  model_section Chapter5

  /-- Right-fibration structure; Chapter 5. -/
  syntax_sort RightFibrationWitness {E : SCat} {B : SCat} (p : Functor E B)
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

namespace SCT

/- Projection API for the admitted adjunction package. -/
internal_defs where
  /-- Unit natural transformation of an adjunction.  Book context: Chapter 5 of the SCT book. -/
  def adjunctionUnit (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C)
    (adj : Adjunction C D L R) : NatTrans C C (idFunctor C) (compFunctor L R) :=
    sorry
  /-- Counit natural transformation of an adjunction.  Book context: Chapter 5 of the SCT book. -/
  def adjunctionCounit (C : SCat) (D : SCat) (L : Functor C D) (R : Functor D C)
    (adj : Adjunction C D L R) : NatTrans D D (compFunctor R L) (idFunctor D) :=
    sorry

end SCT

extend_type_theory SCT where

  model_section Chapter5

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
  syntax_sort CocartesianMorphism {E : SCat} {B : SCat} (p : Functor E B)
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
  syntax_sort CartesianMorphism {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (u : Functor intervalCat E) : Type u
  /-- Locally cocartesian fibration structure; Chapter 5. -/
  syntax_sort LocallyCocartesianFibrationWitness {E : SCat} {B : SCat}
    (p : Functor E B) (fib : Fibration E B p) : Type u
  /-- Locally cartesian fibration structure; Chapter 5. -/
  syntax_sort LocallyCartesianFibrationWitness {E : SCat} {B : SCat}
    (p : Functor E B) (fib : Fibration E B p) : Type u
  /-- Cartesian functor between cartesian fibrations; Chapter 5 dual to cocartesian functors. -/
  syntax_sort CartesianFunctorWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    {E' : SCat} (p' : Functor E' B) (fib' : Fibration E' B p')
    (cart' : CartesianFibrationWitness E' B p' fib') (F : Functor E E') : Type u

  /-- Fiberwise initial-object evidence; Axiom L. -/
  syntax_sort FiberwiseInitialWitness {E : SCat} {B : SCat} (p : Functor E B)
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
    (E' : SCat) (p' : Functor E' B) (F : Functor E E')
    (hBase : FunctorOverBase E B p E' p' F) :
    Functor (directedPullbackCat E B B p (idFunctor B))
      (directedPullbackCat E' B B p' (idFunctor B))
  /-- Beck-Chevalley transformation associated to a functor over the base; Chapter 5 data. -/
  lf_opaque beckChevalleyTransformation (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (E' : SCat) (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E')
    (hBase : FunctorOverBase E B p E' p' F) :
    NatTrans (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E')
      (compFunctor (directedPullbackCat E B B p (idFunctor B))
        (directedPullbackCat E' B B p' (idFunctor B)) (funCat intervalCat E')
        (directedPullbackMapOverBase E B p E' p' F hBase)
        (cocartesianLiftFunctor E' B p' fib' cocart'))
      (compFunctor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E)
        (funCat intervalCat E') (cocartesianLiftFunctor E B p fib cocart)
        (postcompFunctor intervalCat E E' F))
  /-- Beck-Chevalley invertibility for the chosen transformation. -/
  syntax_abbrev CocartesianFunctorBeckChevalley {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    {E' : SCat} (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E')
    (hBase : FunctorOverBase E B p E' p' F) :=
    ObjectwiseNatIso (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E')
      (compFunctor (directedPullbackCat E B B p (idFunctor B))
        (directedPullbackCat E' B B p' (idFunctor B)) (funCat intervalCat E')
        (directedPullbackMapOverBase E B p E' p' F hBase)
        (cocartesianLiftFunctor E' B p' fib' cocart'))
      (compFunctor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E)
        (funCat intervalCat E') (cocartesianLiftFunctor E B p fib cocart)
        (postcompFunctor intervalCat E E' F))
      (beckChevalleyTransformation E B p fib cocart E' p' fib' cocart' F hBase)
  /-- Cocartesian functor between cocartesian fibrations, as over-base data plus the
  Beck-Chevalley invertibility condition. -/
  syntax_abbrev CocartesianFunctorWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    {E' : SCat} (p' : Functor E' B) (fib' : Fibration E' B p')
    (cocart' : CocartesianFibrationWitness E' B p' fib') (F : Functor E E') :=
    Σ hBase : FunctorOverBase E B p E' p' F,
      CocartesianFunctorBeckChevalley E B p fib cocart E' p' fib' cocart' F hBase
  /-- A cocartesian functor lies over the base; source data for the commutative triangle in
  Theorem 6.4.7. -/
  lf_def cocartesianFunctorOverBase : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (fib : Fibration E B p) ⇒ (cocart : CocartesianFibrationWitness E B p fib) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (fib' : Fibration E' B p') ⇒
      (cocart' : CocartesianFibrationWitness E' B p' fib') ⇒ (F : Functor E E') ⇒
      CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F ⇒
        FunctorOverBase E B p E' p' F :=
    fun E B p fib cocart E' p' fib' cocart' F hF => fst hF
  /-- Cocartesian functor witnesses make the Beck-Chevalley transformation invertible. -/
  lf_def cocartesianFunctorBeckChevalley : (E : SCat) ⇒ (B : SCat) ⇒
      (p : Functor E B) ⇒ (fib : Fibration E B p) ⇒
      (cocart : CocartesianFibrationWitness E B p fib) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (fib' : Fibration E' B p') ⇒
      (cocart' : CocartesianFibrationWitness E' B p' fib') ⇒ (F : Functor E E') ⇒
      (hF : CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F) ⇒
        NatIso (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E')
          (compFunctor (directedPullbackCat E B B p (idFunctor B))
            (directedPullbackCat E' B B p' (idFunctor B)) (funCat intervalCat E')
            (directedPullbackMapOverBase E B p E' p' F
              (cocartesianFunctorOverBase E B p fib cocart E' p' fib' cocart' F hF))
            (cocartesianLiftFunctor E' B p' fib' cocart'))
          (compFunctor (directedPullbackCat E B B p (idFunctor B)) (funCat intervalCat E)
            (funCat intervalCat E') (cocartesianLiftFunctor E B p fib cocart)
            (postcompFunctor intervalCat E E' F)) :=
    fun E B p fib cocart E' p' fib' cocart' F hF =>
      ⟨beckChevalleyTransformation E B p fib cocart E' p' fib' cocart' F
        (cocartesianFunctorOverBase E B p fib cocart E' p' fib' cocart' F hF), snd hF⟩
  /-- Fiber map induced by a cocartesian functor over the base. -/
  lf_def cocartesianFunctorFiberMap : (E : SCat) ⇒ (B : SCat) ⇒ (p : Functor E B) ⇒
      (fib : Fibration E B p) ⇒ (cocart : CocartesianFibrationWitness E B p fib) ⇒
      (E' : SCat) ⇒ (p' : Functor E' B) ⇒ (fib' : Fibration E' B p') ⇒
      (cocart' : CocartesianFibrationWitness E' B p' fib') ⇒ (F : Functor E E') ⇒
      (hF : CocartesianFunctorWitness E B p fib cocart E' p' fib' cocart' F) ⇒
      (b : Obj B) ⇒ Functor (fiberCat E B p b) (fiberCat E' B p' b) :=
    fun E B p fib cocart E' p' fib' cocart' F hF b =>
      fiberMap E B p E' p' F
        (cocartesianFunctorOverBase E B p fib cocart E' p' fib' cocart' F hF) b
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
      (compFunctor F G)

extend_type_theory SCT where

  model_section Chapter5

  /-- Fiberwise terminal-object evidence; Axiom L. -/
  syntax_sort FiberwiseTerminalWitness {E : SCat} {B : SCat} (p : Functor E B)
    (fib : Fibration E B p) : Type u
  /-- Cartesian plus fiberwise initial data assembles a left adjoint section; Axiom L. -/
  lf_opaque universal_left_adjoint_section (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (init : FiberwiseInitialWitness E B p fib) : Functor B E
  /-- The left adjoint section lies over the base; Axiom L. -/
  lf_opaque universalLeftSectionBase (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cart : CartesianFibrationWitness E B p fib)
    (init : FiberwiseInitialWitness E B p fib) :
    NatIso (compFunctor (universal_left_adjoint_section E B p fib cart init) p) (idFunctor B)
  /-- Cocartesian plus fiberwise terminal data assembles a right adjoint section; Axiom L. -/
  lf_opaque universal_right_adjoint_section (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (term : FiberwiseTerminalWitness E B p fib) : Functor B E
  /-- The right adjoint section lies over the base; Axiom L. -/
  lf_opaque universalRightSectionBase (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib)
    (term : FiberwiseTerminalWitness E B p fib) :
    NatIso (compFunctor (universal_right_adjoint_section E B p fib cocart term) p) (idFunctor B)
  /-- Contextual fibration indexed by a contextual functor.
  Book context:Chapter 5 of the SCT book.
  -/
  syntax_sort ContextFibration {Γ : SCat} {E : ContextCat Γ} {B : ContextCat Γ}
    (p : ContextFunctor Γ E B) : Type u
  /-- Contextual cartesian fibration witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ContextCartesianFibrationWitness {Γ : SCat} {E : ContextCat Γ} {B : ContextCat Γ}
    (p : ContextFunctor Γ E B) (fib : ContextFibration Γ E B p) : Type u
  /-- Contextual cocartesian fibration witness.  Book context: Chapter 5 of the SCT book. -/
  syntax_sort ContextCocartesianFibrationWitness {Γ : SCat} {E : ContextCat Γ} {B : ContextCat Γ}
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
