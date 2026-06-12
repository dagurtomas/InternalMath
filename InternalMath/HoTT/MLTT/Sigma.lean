/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Pi

/-!
# MLTT dependent pair types

The Σ-type layer, including the non-dependent binary product abbreviation.
-/

@[expose] public section

/-- MLTT with dependent pair types. -/
declare_type_theory MLTT.Sigma extends MLTT.Substitution where

  model_section SigmaTypes

  lf_opaque sigmaTy (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A)) : Ty Γ
  lf_opaque sigmaPair (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A))
    (fstArg : Tm Γ) (sndArg : Tm Γ) : Tm Γ
  lf_opaque sigmaInd (Γ : Ctx) (A : Ty Γ) (B : Ty (extendCtx Γ A))
    (C : Ty (extendCtx Γ (sigmaTy Γ A B)))
    (branch : Tm (extendCtx (extendCtx Γ A) B)) (p : Tm Γ) : Tm Γ

  /-- Cartesian product, defined as the constant-family Σ-type. -/
  lf_def prodTy : (Γ : Ctx) ⇒ Ty Γ ⇒ Ty Γ ⇒ Ty Γ :=
    fun Γ A B => sigmaTy Γ A (weakenTy Γ A B)

  /-- The branch target `C[(x,y)/z]` for Σ-elimination. -/
  lf_def sigmaBranchTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      Ty (extendCtx Γ (sigmaTy Γ A B)) ⇒ Ty (extendCtx (extendCtx Γ A) B) :=
    fun Γ A B C =>
      substTy (extendCtx (extendCtx Γ A) B) (extendCtx Γ (sigmaTy Γ A B))
        (extendSub (extendCtx (extendCtx Γ A) B) Γ
          (compSub (extendCtx (extendCtx Γ A) B) (extendCtx Γ A) Γ
            (weakenSub (extendCtx Γ A) B) (weakenSub Γ A))
          (sigmaTy Γ A B)
          (sigmaPair (extendCtx (extendCtx Γ A) B)
            (weakenTy (extendCtx Γ A) B (weakenTy Γ A A))
            (weakenTy (extendCtx (extendCtx Γ A) B)
              (weakenTy (extendCtx Γ A) B (weakenTy Γ A A))
              (weakenTy (extendCtx Γ A) B B))
            (prevVar Γ A B) (varTop (extendCtx Γ A) B)))
        C

  rule sigma_form {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A)) where
    premise A_ty : IsTy A
    premise B_ty : IsTy B
    conclusion : IsTy (sigmaTy Γ A B)

  rule sigma_intro {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (fstArg : Tm Γ) (sndArg : Tm Γ) where
    premise fst_ty : IsTm fstArg A
    premise snd_ty : IsTm sndArg (substTopTy Γ A B fstArg)
    conclusion : IsTm (sigmaPair Γ A B fstArg sndArg) (sigmaTy Γ A B)

  rule sigma_elim {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (C : Ty (extendCtx Γ (sigmaTy Γ A B)))
      (branch : Tm (extendCtx (extendCtx Γ A) B)) (p : Tm Γ) where
    premise branch_ty : IsTm branch (sigmaBranchTy Γ A B C)
    premise p_ty : IsTm p (sigmaTy Γ A B)
    conclusion : IsTm (sigmaInd Γ A B C branch p) (substTopTy Γ (sigmaTy Γ A B) C p)

  rule sigma_comp {Γ : Ctx} (A : Ty Γ) (B : Ty (extendCtx Γ A))
      (C : Ty (extendCtx Γ (sigmaTy Γ A B)))
      (branch : Tm (extendCtx (extendCtx Γ A) B))
      (fstArg : Tm Γ) (sndArg : Tm Γ) where
    premise branch_ty : IsTm branch (sigmaBranchTy Γ A B C)
    premise fst_ty : IsTm fstArg A
    premise snd_ty : IsTm sndArg (substTopTy Γ A B fstArg)
    conclusion : EqTm
      (sigmaInd Γ A B C branch (sigmaPair Γ A B fstArg sndArg))
      (substTopTm2 Γ A B branch fstArg sndArg)
      (substTopTy Γ (sigmaTy Γ A B) C (sigmaPair Γ A B fstArg sndArg))
