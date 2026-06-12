/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Unit

/-!
# MLTT natural numbers
-/

@[expose] public section

/-- MLTT with the natural-number type. -/
declare_type_theory MLTT.Nat extends MLTT.Substitution where

  model_section NaturalNumbers

  lf_opaque natTy (Γ : Ctx) : Ty Γ
  lf_opaque natZero (Γ : Ctx) : Tm Γ
  lf_opaque natSucc (Γ : Ctx) (n : Tm Γ) : Tm Γ
  lf_opaque natInd (Γ : Ctx) (C : Ty (extendCtx Γ (natTy Γ)))
    (zeroCase : Tm Γ) (succCase : Tm (extendCtx (extendCtx Γ (natTy Γ)) C))
    (n : Tm Γ) : Tm Γ

  /-- The successor branch target `C[succ(x)/x]` for natural-number induction. -/
  lf_def natStepTy : (Γ : Ctx) ⇒ (C : Ty (extendCtx Γ (natTy Γ))) ⇒
      Ty (extendCtx (extendCtx Γ (natTy Γ)) C) :=
    fun Γ C =>
      substTy (extendCtx (extendCtx Γ (natTy Γ)) C) (extendCtx Γ (natTy Γ))
        (extendSub (extendCtx (extendCtx Γ (natTy Γ)) C) Γ
          (compSub (extendCtx (extendCtx Γ (natTy Γ)) C) (extendCtx Γ (natTy Γ)) Γ
            (weakenSub (extendCtx Γ (natTy Γ)) C) (weakenSub Γ (natTy Γ)))
          (natTy Γ) (natSucc (extendCtx (extendCtx Γ (natTy Γ)) C)
            (prevVar Γ (natTy Γ) C)))
        C

  rule nat_form {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTy (natTy Γ)

  rule nat_intro_zero {Γ : Ctx} where
    premise ctx : IsCtx Γ
    conclusion : IsTm (natZero Γ) (natTy Γ)

  rule nat_intro_succ {Γ : Ctx} (n : Tm Γ) where
    premise n_ty : IsTm n (natTy Γ)
    conclusion : IsTm (natSucc Γ n) (natTy Γ)

  rule nat_elim {Γ : Ctx} (C : Ty (extendCtx Γ (natTy Γ)))
      (zeroCase : Tm Γ) (succCase : Tm (extendCtx (extendCtx Γ (natTy Γ)) C))
      (n : Tm Γ) where
    premise zero_ty : IsTm zeroCase (substTopTy Γ (natTy Γ) C (natZero Γ))
    premise succ_ty : IsTm succCase (natStepTy Γ C)
    premise n_ty : IsTm n (natTy Γ)
    conclusion : IsTm (natInd Γ C zeroCase succCase n) (substTopTy Γ (natTy Γ) C n)

  rule nat_comp_zero {Γ : Ctx} (C : Ty (extendCtx Γ (natTy Γ)))
      (zeroCase : Tm Γ) (succCase : Tm (extendCtx (extendCtx Γ (natTy Γ)) C)) where
    premise zero_ty : IsTm zeroCase (substTopTy Γ (natTy Γ) C (natZero Γ))
    premise succ_ty : IsTm succCase (natStepTy Γ C)
    conclusion : EqTm (natInd Γ C zeroCase succCase (natZero Γ)) zeroCase
      (substTopTy Γ (natTy Γ) C (natZero Γ))

  rule nat_comp_succ {Γ : Ctx} (C : Ty (extendCtx Γ (natTy Γ)))
      (zeroCase : Tm Γ) (succCase : Tm (extendCtx (extendCtx Γ (natTy Γ)) C))
      (n : Tm Γ) where
    premise zero_ty : IsTm zeroCase (substTopTy Γ (natTy Γ) C (natZero Γ))
    premise succ_ty : IsTm succCase (natStepTy Γ C)
    premise n_ty : IsTm n (natTy Γ)
    conclusion : EqTm
      (natInd Γ C zeroCase succCase (natSucc Γ n))
      (substTopTm2 Γ (natTy Γ) C succCase n (natInd Γ C zeroCase succCase n))
      (substTopTy Γ (natTy Γ) C (natSucc Γ n))
