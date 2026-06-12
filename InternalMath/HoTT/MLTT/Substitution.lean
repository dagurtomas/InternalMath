/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Basic

/-!
# MLTT structural syntax and rules

This layer extends `MLTT.Basic` with empty and extended contexts, explicit substitutions,
weakening, top-variable substitution, variables, context formation, structural preservation rules,
and judgmental-equality structural rules.
-/

@[expose] public section

/-- MLTT with structural context and substitution operations. -/
declare_type_theory MLTT.Substitution extends MLTT.Basic where

  model_section StructuralSyntax

  lf_opaque emptyCtx : Ctx
  lf_opaque extendCtx (Γ : Ctx) (A : Ty Γ) : Ctx

  /-- Explicit context substitutions, used as metatheoretic reindexing data. -/
  syntax_sort Sub (Γ : Ctx) (Δ : Ctx)

  /-
  InternalLean binder metadata, not an Appendix A.2 inference rule and not a model obligation.
  Variables live in the ordinary context zone and have raw-term syntax.
  -/
  context_zone ordinary : Ctx
  binder_class ordinary_var : Tm in ordinary

  lf_opaque idSub (Γ : Ctx) : Sub Γ Γ
  lf_opaque compSub (Γ : Ctx) (Δ : Ctx) (Θ : Ctx) (σ : Sub Γ Δ) (τ : Sub Δ Θ) :
      Sub Γ Θ
  lf_opaque weakenSub (Γ : Ctx) (A : Ty Γ) : Sub (extendCtx Γ A) Γ
  lf_opaque substTy (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (A : Ty Δ) : Ty Γ
  lf_opaque substTm (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (t : Tm Δ) : Tm Γ
  lf_opaque extendSub (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (A : Ty Δ) (t : Tm Γ) :
      Sub Γ (extendCtx Δ A)

  /-- Weakening of a type along one context extension. -/
  lf_def weakenTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty Γ ⇒ Ty (extendCtx Γ A) :=
    fun Γ A B => substTy (extendCtx Γ A) Γ (weakenSub Γ A) B

  /-- Weakening of a term along one context extension. -/
  lf_def weakenTm : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm Γ ⇒ Tm (extendCtx Γ A) :=
    fun Γ A t => substTm (extendCtx Γ A) Γ (weakenSub Γ A) t

  /-- The newest variable in an extended context. -/
  lf_opaque varTop (Γ : Ctx) (A : Ty Γ) : Tm (extendCtx Γ A)

  /-- Capture-avoiding substitution of one term for the newest variable in a type. -/
  lf_def substTopTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty (extendCtx Γ A) ⇒ Tm Γ ⇒ Ty Γ :=
    fun Γ A B arg => substTy Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg) B

  /-- Capture-avoiding substitution of one term for the newest variable in a term. -/
  lf_def substTopTm : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (extendCtx Γ A) ⇒ Tm Γ ⇒ Tm Γ :=
    fun Γ A body arg => substTm Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg) body

  /-- Simultaneous substitution for the two newest variables in a type. -/
  lf_def substTopTy2 : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      Ty (extendCtx (extendCtx Γ A) B) ⇒ Tm Γ ⇒ Tm Γ ⇒ Ty Γ :=
    fun Γ A B C arg1 arg2 =>
      substTy Γ (extendCtx (extendCtx Γ A) B)
        (extendSub Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg1) B arg2) C

  /-- Simultaneous substitution for the two newest variables in a term. -/
  lf_def substTopTm2 : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      Tm (extendCtx (extendCtx Γ A) B) ⇒ Tm Γ ⇒ Tm Γ ⇒ Tm Γ :=
    fun Γ A B body arg1 arg2 =>
      substTm Γ (extendCtx (extendCtx Γ A) B)
        (extendSub Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg1) B arg2) body

  /-- Simultaneous substitution for the three newest variables in a type. -/
  lf_def substTopTy3 : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒
      Ty (extendCtx (extendCtx (extendCtx Γ A) B) C) ⇒ Tm Γ ⇒ Tm Γ ⇒ Tm Γ ⇒ Ty Γ :=
    fun Γ A B C D arg1 arg2 arg3 =>
      substTy Γ (extendCtx (extendCtx (extendCtx Γ A) B) C)
        (extendSub Γ (extendCtx (extendCtx Γ A) B)
          (extendSub Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg1) B arg2)
          C arg3)
        D

  /-- Simultaneous substitution for the three newest variables in a term. -/
  lf_def substTopTm3 : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒
      Tm (extendCtx (extendCtx (extendCtx Γ A) B) C) ⇒ Tm Γ ⇒ Tm Γ ⇒ Tm Γ ⇒ Tm Γ :=
    fun Γ A B C body arg1 arg2 arg3 =>
      substTm Γ (extendCtx (extendCtx (extendCtx Γ A) B) C)
        (extendSub Γ (extendCtx (extendCtx Γ A) B)
          (extendSub Γ (extendCtx Γ A) (extendSub Γ Γ (idSub Γ) A arg1) B arg2)
          C arg3)
        body

  /-- The previous variable in a context extended twice. -/
  lf_def prevVar : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      Tm (extendCtx (extendCtx Γ A) B) :=
    fun Γ A B => weakenTm (extendCtx Γ A) B (varTop Γ A)

  model_section ContextFormation

  rule ctx_EMP where
    conclusion : IsCtx emptyCtx

  rule ctx_EXT {Γ : Ctx} (A : Ty Γ) where
    premise ctx : IsCtx Γ
    premise ty : IsTy A
    conclusion : IsCtx (extendCtx Γ A)

  model_section StructuralRules

  rule substTy_form {Γ : Ctx} {A : Ty Γ} (a : Tm Γ) (B : Ty (extendCtx Γ A)) where
    premise a_ty : IsTm a A
    premise B_ty : IsTy B
    conclusion : IsTy (substTopTy Γ A B a)

  rule wkgTy_form {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) where
    premise B_ty : IsTy B
    conclusion : IsTy (weakenTy Γ A B)

  rule vble {Γ : Ctx} (A : Ty Γ) where
    premise ctx : IsCtx (extendCtx Γ A)
    conclusion : IsTm (varTop Γ A) (weakenTy Γ A A)

  rule subst_1 {Γ : Ctx} {A : Ty Γ} (a : Tm Γ) (B : Ty (extendCtx Γ A))
      (b : Tm (extendCtx Γ A)) where
    premise a_ty : IsTm a A
    premise b_ty : IsTm b B
    conclusion : IsTm (substTopTm Γ A b a) (substTopTy Γ A B a)

  rule wkg_1 {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) (b : Tm Γ) where
    premise b_ty : IsTm b B
    conclusion : IsTm (weakenTm Γ A b) (weakenTy Γ A B)

  rule subst_2 {Γ : Ctx} {A : Ty Γ} (a : Tm Γ) (B : Ty (extendCtx Γ A))
      (b : Tm (extendCtx Γ A)) (c : Tm (extendCtx Γ A)) where
    premise a_ty : IsTm a A
    premise h : EqTm b c B
    conclusion : EqTm (substTopTm Γ A b a) (substTopTm Γ A c a) (substTopTy Γ A B a)

  rule subst_3 {Γ : Ctx} {A : Ty Γ} (a : Tm Γ) (b : Tm Γ)
      (C : Ty (extendCtx Γ A)) (c : Tm (extendCtx Γ A)) where
    premise h : EqTm a b A
    premise c_ty : IsTm c C
    conclusion : EqTm (substTopTm Γ A c a) (substTopTm Γ A c b) (substTopTy Γ A C a)

  rule wkg_2 {Γ : Ctx} (A : Ty Γ) (B : Ty Γ) (b : Tm Γ) (c : Tm Γ) where
    premise h : EqTm b c B
    conclusion : EqTm (weakenTm Γ A b) (weakenTm Γ A c) (weakenTy Γ A B)

  model_section Equality

  rule eq_refl {Γ : Ctx} (a : Tm Γ) (A : Ty Γ) where
    premise typed : IsTm a A
    conclusion : EqTm a a A

  rule eq_symm {Γ : Ctx} (a : Tm Γ) (b : Tm Γ) (A : Ty Γ) where
    premise h : EqTm a b A
    conclusion : EqTm b a A

  rule eq_trans {Γ : Ctx} (a : Tm Γ) (b : Tm Γ) (c : Tm Γ) (A : Ty Γ) where
    premise left : EqTm a b A
    premise right : EqTm b c A
    conclusion : EqTm a c A
