/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Substitution

/-!
# MLTT empty type
-/

@[expose] public section

/-- MLTT with the empty type. -/
declare_type_theory MLTT.Empty extends MLTT.Substitution where

  model_section EmptyType

  lf_opaque emptyTy (Γ : Ctx) : Ty Γ
  lf_opaque emptyInd (Γ : Ctx) (C : Ty (extendCtx Γ (emptyTy Γ))) (a : Tm Γ) : Tm Γ

  rule empty_form {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTy (emptyTy Γ)

  rule empty_elim {Γ : Ctx} (C : Ty (extendCtx Γ (emptyTy Γ))) (a : Tm Γ) where
    premise absurd : IsTm a (emptyTy Γ)
    conclusion : IsTm (emptyInd Γ C a) (substTopTy Γ (emptyTy Γ) C a)
