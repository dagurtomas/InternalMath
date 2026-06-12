/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Substitution

/-!
# MLTT dependent function types

The Π-type layer over the structural MLTT core.  Because current InternalLean composition does not
support diamond-shaped mixins with shared ancestry, this layer linearly extends
`MLTT.Substitution`.
-/

@[expose] public section

/-- MLTT with dependent function types. -/
declare_type_theory MLTT.Pi extends MLTT.Substitution where

  model_section PiTypes

  lf_opaque piTy (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A)) : Ty Γ
  lf_opaque lam (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A))
    (body : Tm (extendCtx Γ A)) : Tm Γ
  lf_opaque app (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A))
    (fn : Tm Γ) (arg : Tm Γ) : Tm Γ

  /-- Non-dependent function type, defined as the constant-family Π-type. -/
  lf_def arrowTy : (Γ : Ctx) ⇒ Ty Γ ⇒ Ty Γ ⇒ Ty Γ :=
    fun Γ A B => piTy Γ A (weakenTy Γ A B)

  rule pi_form {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A)) where
    premise A_ty : IsTy A
    premise B_ty : IsTy B
    conclusion : IsTy (piTy Γ A B)

  rule pi_intro {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (body : Tm (extendCtx Γ A)) where
    premise body_ty : IsTm body B
    conclusion : IsTm (lam Γ A B body) (piTy Γ A B)

  rule pi_elim {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (fn : Tm Γ) (arg : Tm Γ) where
    premise fn_ty : IsTm fn (piTy Γ A B)
    premise arg_ty : IsTm arg A
    conclusion : IsTm (app Γ A B fn arg) (substTopTy Γ A B arg)

  rule pi_comp {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (body : Tm (extendCtx Γ A)) (arg : Tm Γ) where
    premise body_ty : IsTm body B
    premise arg_ty : IsTm arg A
    conclusion : EqTm (app Γ A B (lam Γ A B body) arg)
      (substTopTm Γ A body arg) (substTopTy Γ A B arg)

  rule pi_uniq {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A)) (fn : Tm Γ) where
    premise fn_ty : IsTm fn (piTy Γ A B)
    conclusion : EqTm fn
      (lam Γ A B (app (extendCtx Γ A) (weakenTy Γ A A)
        (substTy (extendCtx (extendCtx Γ A) (weakenTy Γ A A)) (extendCtx Γ A)
          (weakenSub (extendCtx Γ A) (weakenTy Γ A A)) B)
        (weakenTm Γ A fn) (varTop Γ A)))
      (piTy Γ A B)

  rule pi_intro_eq {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (body : Tm (extendCtx Γ A)) (body' : Tm (extendCtx Γ A)) where
    premise h : EqTm body body' B
    conclusion : EqTm (lam Γ A B body) (lam Γ A B body') (piTy Γ A B)
