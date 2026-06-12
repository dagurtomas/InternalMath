/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Substitution

/-!
# MLTT unit type
-/

@[expose] public section

/-- MLTT with the unit type. -/
declare_type_theory MLTT.Unit extends MLTT.Substitution where

  model_section UnitType

  lf_opaque unitTy (Γ : Ctx) : Ty Γ
  lf_opaque unitStar (Γ : Ctx) : Tm Γ
  lf_opaque unitInd (Γ : Ctx) (C : Ty (extendCtx Γ (unitTy Γ)))
    (center : Tm Γ) (a : Tm Γ) : Tm Γ

  rule unit_form {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTy (unitTy Γ)

  rule unit_intro {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTm (unitStar Γ) (unitTy Γ)

  rule unit_elim {Γ : Ctx} (C : Ty (extendCtx Γ (unitTy Γ)))
      (center : Tm Γ) (a : Tm Γ) where
    premise center_ty : IsTm center (substTopTy Γ (unitTy Γ) C (unitStar Γ))
    premise a_ty : IsTm a (unitTy Γ)
    conclusion : IsTm (unitInd Γ C center a) (substTopTy Γ (unitTy Γ) C a)

  rule unit_comp {Γ : Ctx} (C : Ty (extendCtx Γ (unitTy Γ))) (center : Tm Γ) where
    premise center_ty : IsTm center (substTopTy Γ (unitTy Γ) C (unitStar Γ))
    conclusion : EqTm (unitInd Γ C center (unitStar Γ)) center
      (substTopTy Γ (unitTy Γ) C (unitStar Γ))
