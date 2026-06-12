/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Library

/-!
# Homotopy type theory, HoTT book Appendix A.3

This file implements the HoTT layer from Appendix A.3 of the HoTT book on top of the separated
`Ty`/`Tm` MLTT core.  A.3 adds function extensionality, univalence, and the circle higher
inductive type.  MLTT library definitions provide the prerequisite notions such as equivalences,
`happly`, `idtoeqv`, dependent paths, transport, and `apd`.
-/

@[expose] public section

/-- Homotopy type theory as Appendix A.2 MLTT plus the Appendix A.3 axioms and circle HIT. -/
declare_type_theory HoTT extends MLTT where

  /-- Function extensionality and univalence as primitive constants. -/
  model_section AxiomConstants

  /-- `funext(f,g) : isequiv(happly_{f,g})` when `f,g : Π(x:A). B`. -/
  lf_opaque funext (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A))
    (f : Tm Γ) (g : Tm Γ) : Tm Γ

  rule pi_ext {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (f : Tm Γ) (g : Tm Γ) where
    premise f_ty : IsTm f (piTy Γ A B)
    premise g_ty : IsTm g (piTy Γ A B)
    conclusion : IsTm (funext Γ A B f g)
      (isequiv Γ (idTy Γ (piTy Γ A B) f g) (happlyCodTy Γ A B f g)
        (happly Γ A B f g))

  /-- `univalence(A,B) : isequiv(idtoeqv_{A,B})` for types represented at universe level `i`. -/
  lf_opaque univalence (Γ : Ctx) (i : UnivLevel) (A : Ty Γ) (B : Ty Γ) : Tm Γ

  rule univ_univ {Γ : Ctx} (i : UnivLevel) (A : Ty Γ) (B : Ty Γ) where
    premise ctx : IsCtx Γ
    conclusion : IsTm (univalence Γ i A B)
      (isequiv Γ (universePathTy Γ i A B) (equivTy Γ A B) (idtoeqv Γ i A B))

  /-- The circle higher inductive type. -/
  model_section Circle

  lf_opaque circleTy (Γ : Ctx) : Ty Γ
  lf_opaque circleBase (Γ : Ctx) : Tm Γ
  lf_opaque circleLoop (Γ : Ctx) : Tm Γ

  rule circle_form {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTy (circleTy Γ)

  rule circle_intro_base {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTm (circleBase Γ) (circleTy Γ)

  rule circle_intro_loop {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTm (circleLoop Γ) (idTy Γ (circleTy Γ) (circleBase Γ) (circleBase Γ))

  /-- The dependent-path type `b =^C_loop b` used by the circle eliminator. -/
  lf_def circleDepPathTy : (Γ : Ctx) ⇒ Ty (extendCtx Γ (circleTy Γ)) ⇒ Tm Γ ⇒ Ty Γ :=
    fun Γ C baseCase =>
      depPathTy Γ (circleTy Γ) C (circleBase Γ) (circleBase Γ) (circleLoop Γ)
        baseCase baseCase

  /-- The circle eliminator `ind_S¹(x.C, b, ℓ, p)`. -/
  lf_opaque circleInd (Γ : Ctx)
    (C : Ty (extendCtx Γ (circleTy Γ)))
    (baseCase : Tm Γ) (loopCase : Tm Γ) (p : Tm Γ) : Tm Γ

  rule circle_elim {Γ : Ctx} (C : Ty (extendCtx Γ (circleTy Γ)))
      (baseCase : Tm Γ) (loopCase : Tm Γ) (p : Tm Γ) where
    premise base_ty : IsTm baseCase (substTopTy Γ (circleTy Γ) C (circleBase Γ))
    premise loop_ty : IsTm loopCase (circleDepPathTy Γ C baseCase)
    premise p_ty : IsTm p (circleTy Γ)
    conclusion : IsTm (circleInd Γ C baseCase loopCase p)
      (substTopTy Γ (circleTy Γ) C p)

  rule circle_comp_base {Γ : Ctx} (C : Ty (extendCtx Γ (circleTy Γ)))
      (baseCase : Tm Γ) (loopCase : Tm Γ) where
    premise base_ty : IsTm baseCase (substTopTy Γ (circleTy Γ) C (circleBase Γ))
    premise loop_ty : IsTm loopCase (circleDepPathTy Γ C baseCase)
    conclusion : EqTm (circleInd Γ C baseCase loopCase (circleBase Γ)) baseCase
      (substTopTy Γ (circleTy Γ) C (circleBase Γ))

  /-- Context `Γ, y:S¹, x:S¹` used to describe the dependent action on the circle loop. -/
  lf_def circleTwiceCtx : Ctx ⇒ Ctx :=
    fun Γ => extendCtx (extendCtx Γ (circleTy Γ)) (circleTy (extendCtx Γ (circleTy Γ)))

  /-- Projection from `Γ, y:S¹, x:S¹` to `Γ`. -/
  lf_def circleLoopBaseSub : (Γ : Ctx) ⇒ Sub (circleTwiceCtx Γ) Γ :=
    fun Γ =>
      compSub (circleTwiceCtx Γ) (extendCtx Γ (circleTy Γ)) Γ
        (weakenSub (extendCtx Γ (circleTy Γ)) (circleTy (extendCtx Γ (circleTy Γ))))
        (weakenSub Γ (circleTy Γ))

  /-- Substitution sending the motive variable to the newest circle variable. -/
  lf_def circleLoopPointSub :
      (Γ : Ctx) ⇒ Sub (circleTwiceCtx Γ) (extendCtx Γ (circleTy Γ)) :=
    fun Γ =>
      extendSub (circleTwiceCtx Γ) Γ (circleLoopBaseSub Γ) (circleTy Γ)
        (varTop (extendCtx Γ (circleTy Γ)) (circleTy (extendCtx Γ (circleTy Γ))))

  /-- The motive `C` reindexed to context `Γ, y:S¹, x:S¹`. -/
  lf_def circleIndLoopMotive : (Γ : Ctx) ⇒
      Ty (extendCtx Γ (circleTy Γ)) ⇒ Ty (circleTwiceCtx Γ) :=
    fun Γ C => substTy (circleTwiceCtx Γ) (extendCtx Γ (circleTy Γ))
      (circleLoopPointSub Γ) C

  /-- The body `ind_S¹(x.C,b,ℓ,y)` in context `Γ, y:S¹`. -/
  lf_def circleIndLoopBody : (Γ : Ctx) ⇒
      (C : Ty (extendCtx Γ (circleTy Γ))) ⇒ Tm Γ ⇒ Tm Γ ⇒
      Tm (extendCtx Γ (circleTy Γ)) :=
    fun Γ C baseCase loopCase =>
      circleInd (extendCtx Γ (circleTy Γ)) (circleIndLoopMotive Γ C)
        (weakenTm Γ (circleTy Γ) baseCase) (weakenTm Γ (circleTy Γ) loopCase)
        (varTop Γ (circleTy Γ))

  /-- The term `apd(λ y. ind_S¹(x.C,b,ℓ,y))(loop)`. -/
  lf_def circleApdLoop : (Γ : Ctx) ⇒
      Ty (extendCtx Γ (circleTy Γ)) ⇒ Tm Γ ⇒ Tm Γ ⇒ Tm Γ :=
    fun Γ C baseCase loopCase =>
      apd Γ (circleTy Γ) C (circleIndLoopBody Γ C baseCase loopCase)
        (circleBase Γ) (circleBase Γ) (circleLoop Γ)

  /-- The propositional circle loop computation term, indexed by the motive universe level. -/
  lf_opaque circleLoopComp (Γ : Ctx) (i : UnivLevel)
    (C : Ty (extendCtx Γ (circleTy Γ)))
    (baseCase : Tm Γ) (loopCase : Tm Γ) : Tm Γ

  rule circle_comp_loop {Γ : Ctx} (i : UnivLevel)
      (C : Ty (extendCtx Γ (circleTy Γ))) (baseCase : Tm Γ) (loopCase : Tm Γ) where
    premise base_ty : IsTm baseCase (substTopTy Γ (circleTy Γ) C (circleBase Γ))
    premise loop_ty : IsTm loopCase (circleDepPathTy Γ C baseCase)
    conclusion : IsTm (circleLoopComp Γ i C baseCase loopCase)
      (idTy Γ (circleDepPathTy Γ C baseCase) (circleApdLoop Γ C baseCase loopCase) loopCase)
