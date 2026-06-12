/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Substitution

/-!
# MLTT identity types
-/

@[expose] public section

/-- MLTT with identity types. -/
declare_type_theory MLTT.Identity extends MLTT.Substitution where

  model_section IdentityTypes

  lf_opaque idTy (Γ : Ctx) (A : Ty Γ) (a : Tm Γ) (b : Tm Γ) : Ty Γ
  lf_opaque refl (Γ : Ctx) (a : Tm Γ) : Tm Γ

  /-- The path type `x =_A y` in context `Γ, x:A, y:A`. -/
  lf_def idMotivePathTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒
      Ty (extendCtx (extendCtx Γ A) (weakenTy Γ A A)) :=
    fun Γ A =>
      idTy (extendCtx (extendCtx Γ A) (weakenTy Γ A A))
        (weakenTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A A))
        (prevVar Γ A (weakenTy Γ A A))
        (varTop (extendCtx Γ A) (weakenTy Γ A A))

  /-- The context `Γ, x:A, y:A, p:x =_A y` for the identity eliminator motive. -/
  lf_def idMotiveCtx : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ctx :=
    fun Γ A => extendCtx (extendCtx (extendCtx Γ A) (weakenTy Γ A A))
      (idMotivePathTy Γ A)

  /-- The reflexivity path `refl_z` in context `Γ,z:A`. -/
  lf_def idReflPath : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (extendCtx Γ A) :=
    fun Γ A => refl (extendCtx Γ A) (varTop Γ A)

  /-- The branch target `C[z,z,refl_z/x,y,p]` in context `Γ,z:A`. -/
  lf_def idReflBranchTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒
      Ty (idMotiveCtx Γ A) ⇒ Ty (extendCtx Γ A) :=
    fun Γ A C =>
      substTopTy2 (extendCtx Γ A) (weakenTy Γ A A) (idMotivePathTy Γ A)
        C (varTop Γ A) (idReflPath Γ A)

  /-- The eliminator target `C[a,b,p/x,y,p]`. -/
  lf_def idIndTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty (idMotiveCtx Γ A) ⇒
      Tm Γ ⇒ Tm Γ ⇒ Tm Γ ⇒ Ty Γ :=
    fun Γ A C a b p =>
      substTopTy3 Γ A (weakenTy Γ A A) (idMotivePathTy Γ A) C a b p

  /-- Identity eliminator. -/
  lf_opaque idInd (Γ : Ctx) (A : Ty Γ) (C : Ty (idMotiveCtx Γ A))
    (reflCase : Tm (extendCtx Γ A)) (a : Tm Γ) (b : Tm Γ) (p : Tm Γ) : Tm Γ

  rule id_form {Γ : Ctx} (A : Ty Γ) (a : Tm Γ) (b : Tm Γ) where
    premise A_ty : IsTy A
    premise a_ty : IsTm a A
    premise b_ty : IsTm b A
    conclusion : IsTy (idTy Γ A a b)

  rule id_intro {Γ : Ctx} (A : Ty Γ) (a : Tm Γ) where
    premise term : IsTm a A
    conclusion : IsTm (refl Γ a) (idTy Γ A a a)

  rule id_elim {Γ : Ctx} (A : Ty Γ) (C : Ty (idMotiveCtx Γ A))
      (reflCase : Tm (extendCtx Γ A)) (a : Tm Γ) (b : Tm Γ) (p : Tm Γ) where
    premise refl_ty : IsTm reflCase (idReflBranchTy Γ A C)
    premise left : IsTm a A
    premise right : IsTm b A
    premise path : IsTm p (idTy Γ A a b)
    conclusion : IsTm (idInd Γ A C reflCase a b p) (idIndTy Γ A C a b p)

  rule id_comp {Γ : Ctx} (A : Ty Γ) (C : Ty (idMotiveCtx Γ A))
      (reflCase : Tm (extendCtx Γ A)) (a : Tm Γ) where
    premise refl_ty : IsTm reflCase (idReflBranchTy Γ A C)
    premise term : IsTm a A
    conclusion : EqTm
      (idInd Γ A C reflCase a a (refl Γ a))
      (substTopTm Γ A reflCase a)
      (idIndTy Γ A C a a (refl Γ a))
