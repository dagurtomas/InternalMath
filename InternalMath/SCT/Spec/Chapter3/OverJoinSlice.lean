/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter3.Localization

/-!
# Chapter 3 exponentiable functors, joins, and slices

This file records the Chapter 3 structures after localization: exponentiable functors, joins,
relative joins, and over/slice categories.

Book guide, paraphrasing the May 2026 draft:

- Definition 3.5.7 introduces exponentiable functors. The witness is `ExponentiableFunctor`; the
  dependent-product package is `dependentProductOverPackage`, with projections
  `dependentProductOverCat` and `dependentProductOverProjection`.
- Axioms J.1 and J.2 give joins. The basic constructor is `joinCat`, with inclusions `joinInl` and
  `joinInr`, pushout comparison `joinPushoutSquare`, mapping-out equivalence
  `joinMappingEquiv`, and descender data `joinDesc`, `joinDescBetaLeft`, `joinDescBetaRight`, and
  `joinDescUniq`.
- The interval is the join of two terminal categories; the comparison is
  `intervalJoinEquiv` with its forward/backward maps and unit/counit.
- `dependentProductFunctor`, `dependentProductBeckChevalley`, `relativeJoinCat`,
  `relativeJoinInl`, and `relativeJoinInr` are admitted internal declarations for the over-category
  and relative-join API.
-/

@[expose] public section

extend_type_theory SCT where

  model_section Chapter3

  /-- Exponentiable functor witness; Definition 3.5.7. -/
  syntax_sort ExponentiableFunctor (A : SCat) (B : SCat) (u : Functor A B) : Type u
  /-- Dependent-product package along an exponentiable functor.  It stores the
  dependent product category over the codomain and its projection; the universal property is part
  of the exponentiability data.  Book target: Definition 3.5.4 and Definition 3.5.7. -/
  lf_opaque dependentProductOverPackage (A : SCat) (B : SCat) (E : SCat)
    (u : Functor A B) (p : Functor E A) (exp : ExponentiableFunctor A B u) :
    Σ Pdt : SCat, Functor Pdt B
  /-- Dependent product along an exponentiable map over a base. -/
  lf_def dependentProductOverCat : (A : SCat) ⇒ (B : SCat) ⇒ (E : SCat) ⇒
      (u : Functor A B) ⇒ (p : Functor E A) ⇒ ExponentiableFunctor A B u ⇒ SCat :=
    fun A B E u p exp => fst (dependentProductOverPackage A B E u p exp)
  /-- Projection of a dependent product over the codomain. -/
  lf_def dependentProductOverProjection : (A : SCat) ⇒ (B : SCat) ⇒ (E : SCat) ⇒
      (u : Functor A B) ⇒ (p : Functor E A) ⇒ (exp : ExponentiableFunctor A B u) ⇒
        Functor (dependentProductOverCat A B E u p exp) B :=
    fun A B E u p exp => snd (dependentProductOverPackage A B E u p exp)

  /-- Join of synthetic categories; Axioms J.1 and J.2. -/
  lf_opaque joinCat (C : SCat) (D : SCat) : SCat

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- Pullback/reindexing functor between over-categories.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove from exponentiability of the base functor. -/
  def overPullbackFunctor (A : SCat) (B : SCat) (u : Functor A B) :
    Functor (overCat B) (overCat A) := sorry
  /-- Dependent product functor right adjoint to pullback for an exponentiable functor.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove from exponentiability of the base functor. -/
  def dependentProductFunctor (A : SCat) (B : SCat)
    (u : Functor A B) (exp : ExponentiableFunctor A B u) : Functor (overCat A) (overCat B) := sorry
  /-- Beck-Chevalley comparison for dependent products; Construction 3.5.6.
  Book target: Construction 3.5.6, pullback/reindexing, dependent product, and Beck-Chevalley
  comparison.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove from exponentiability of the base functor. -/
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
  /-- Package for the mapping-in dependent-product side of Axiom J.2. -/
  lf_opaque joinDependentProductPackage (C : SCat) (D : SCat) (E : SCat) :
    Σ J : SCat, CatEquiv (funCat E (joinCat C D)) J
  /-- Category for the mapping-in dependent-product side of Axiom J.2. -/
  lf_def joinDependentProductCat : (C : SCat) ⇒ (D : SCat) ⇒ (E : SCat) ⇒ SCat :=
    fun C D E => fst (joinDependentProductPackage C D E)
  /-- Join-dependent-product universal property; Axiom J.2. -/
  lf_def joinDependentProductEquiv : (C : SCat) ⇒ (D : SCat) ⇒ (E : SCat) ⇒
      CatEquiv (funCat E (joinCat C D)) (joinDependentProductCat C D E) :=
    fun C D E => snd (joinDependentProductPackage C D E)

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
  To finish this declaration: define from dependent products and the ordinary join interface. -/
  def relativeJoinCat (B : SCat) (C : SCat) (D : SCat)
    (p : Functor C B) (q : Functor D B) : SCat := sorry
  /-- Left inclusion into a relative join.
  Book target: Proposition 3.5.15 and Corollary 3.5.16, relative joins as dependent-product
  constructions.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: define from dependent products and the ordinary join interface. -/
  def relativeJoinInl (B : SCat) (C : SCat) (D : SCat)
    (p : Functor C B) (q : Functor D B) : Functor C (relativeJoinCat B C D p q) := sorry
  /-- Right inclusion into a relative join.
  Book target: Proposition 3.5.15 and Corollary 3.5.16, relative joins as dependent-product
  constructions.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: define from dependent products and the ordinary join interface. -/
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
