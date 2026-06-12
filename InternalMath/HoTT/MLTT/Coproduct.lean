/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Substitution

/-!
# MLTT coproduct types
-/

@[expose] public section

/-- MLTT with binary coproduct types. -/
declare_type_theory MLTT.Coproduct extends MLTT.Substitution where

  model_section CoproductTypes

  lf_opaque coprodTy (Γ : Ctx) (A : Ty Γ) (B : Ty Γ) : Ty Γ
  lf_opaque coprodInl (Γ : Ctx) (A : Ty Γ) (B : Ty Γ) (a : Tm Γ) : Tm Γ
  lf_opaque coprodInr (Γ : Ctx) (A : Ty Γ) (B : Ty Γ) (b : Tm Γ) : Tm Γ
  lf_opaque coprodInd (Γ : Ctx) (A : Ty Γ) (B : Ty Γ)
    (C : Ty (extendCtx Γ (coprodTy Γ A B)))
    (left : Tm (extendCtx Γ A)) (right : Tm (extendCtx Γ B)) (e : Tm Γ) : Tm Γ

  /-- The left branch target `C[inl(x)/z]` for coproduct elimination. -/
  lf_def coprodInlBranchTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒
      Ty (extendCtx Γ (coprodTy Γ A B)) ⇒ Ty (extendCtx Γ A) :=
    fun Γ A B C =>
      substTy (extendCtx Γ A) (extendCtx Γ (coprodTy Γ A B))
        (extendSub (extendCtx Γ A) Γ (weakenSub Γ A) (coprodTy Γ A B)
          (coprodInl (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A B)
            (varTop Γ A)))
        C

  /-- The right branch target `C[inr(y)/z]` for coproduct elimination. -/
  lf_def coprodInrBranchTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒
      Ty (extendCtx Γ (coprodTy Γ A B)) ⇒ Ty (extendCtx Γ B) :=
    fun Γ A B C =>
      substTy (extendCtx Γ B) (extendCtx Γ (coprodTy Γ A B))
        (extendSub (extendCtx Γ B) Γ (weakenSub Γ B) (coprodTy Γ A B)
          (coprodInr (extendCtx Γ B) (weakenTy Γ B A) (weakenTy Γ B B)
            (varTop Γ B)))
        C

  rule coprod_form {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) where
    premise A_ty : IsTy A
    premise B_ty : IsTy B
    conclusion : IsTy (coprodTy Γ A B)

  rule coprod_intro_left {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) (a : Tm Γ) where
    premise term : IsTm a A
    conclusion : IsTm (coprodInl Γ A B a) (coprodTy Γ A B)

  rule coprod_intro_right {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) (b : Tm Γ) where
    premise term : IsTm b B
    conclusion : IsTm (coprodInr Γ A B b) (coprodTy Γ A B)

  rule coprod_elim {Γ : Ctx} (A : Ty Γ) (B : Ty Γ)
      (C : Ty (extendCtx Γ (coprodTy Γ A B)))
      (left : Tm (extendCtx Γ A)) (right : Tm (extendCtx Γ B)) (e : Tm Γ) where
    premise left_ty : IsTm left (coprodInlBranchTy Γ A B C)
    premise right_ty : IsTm right (coprodInrBranchTy Γ A B C)
    premise e_ty : IsTm e (coprodTy Γ A B)
    conclusion : IsTm (coprodInd Γ A B C left right e)
      (substTopTy Γ (coprodTy Γ A B) C e)

  rule coprod_comp_left {Γ : Ctx} (A : Ty Γ) (B : Ty Γ)
      (C : Ty (extendCtx Γ (coprodTy Γ A B)))
      (left : Tm (extendCtx Γ A)) (right : Tm (extendCtx Γ B)) (a : Tm Γ) where
    premise left_ty : IsTm left (coprodInlBranchTy Γ A B C)
    premise a_ty : IsTm a A
    conclusion : EqTm
      (coprodInd Γ A B C left right (coprodInl Γ A B a))
      (substTopTm Γ A left a)
      (substTopTy Γ (coprodTy Γ A B) C (coprodInl Γ A B a))

  rule coprod_comp_right {Γ : Ctx} (A : Ty Γ) (B : Ty Γ)
      (C : Ty (extendCtx Γ (coprodTy Γ A B)))
      (left : Tm (extendCtx Γ A)) (right : Tm (extendCtx Γ B)) (b : Tm Γ) where
    premise right_ty : IsTm right (coprodInrBranchTy Γ A B C)
    premise b_ty : IsTm b B
    conclusion : EqTm
      (coprodInd Γ A B C left right (coprodInr Γ A B b))
      (substTopTm Γ B right b)
      (substTopTy Γ (coprodTy Γ A B) C (coprodInr Γ A B b))
