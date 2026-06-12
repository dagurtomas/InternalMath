/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT

/-!
# Derived structural MLTT operations

This file adds notation-level structural helpers over the explicit substitution API in the MLTT
core.  These are checked `lf_def`s, not new primitive syntax or model fields.
-/

@[expose] public section

extend_type_theory MLTT where

  /-- The variable two positions below the top in a context extended three times. -/
  lf_def prev2Var :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒
      Tm (extendCtx (extendCtx (extendCtx Γ A) B) C) :=
    fun Γ A B C => weakenTm (extendCtx (extendCtx Γ A) B) C (prevVar Γ A B)

  /-- The variable three positions below the top in a context extended four times. -/
  lf_def prev3Var :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒
      (D : Ty (extendCtx (extendCtx (extendCtx Γ A) B) C)) ⇒
      Tm (extendCtx (extendCtx (extendCtx (extendCtx Γ A) B) C) D) :=
    fun Γ A B C D =>
      weakenTm (extendCtx (extendCtx (extendCtx Γ A) B) C) D (prev2Var Γ A B C)

  /-- Projection from `Γ,x:A` to `Γ`. -/
  lf_def wk1Sub : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Sub (extendCtx Γ A) Γ :=
    fun Γ A => weakenSub Γ A

  /-- Projection from `Γ,x:A,y:B` to `Γ`. -/
  lf_def wk2Sub :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      Sub (extendCtx (extendCtx Γ A) B) Γ :=
    fun Γ A B => compSub (extendCtx (extendCtx Γ A) B) (extendCtx Γ A) Γ
      (weakenSub (extendCtx Γ A) B) (weakenSub Γ A)

  /-- Projection from `Γ,x:A,y:B,z:C` to `Γ`. -/
  lf_def wk3Sub :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒
      Sub (extendCtx (extendCtx (extendCtx Γ A) B) C) Γ :=
    fun Γ A B C => compSub (extendCtx (extendCtx (extendCtx Γ A) B) C)
      (extendCtx (extendCtx Γ A) B) Γ
      (weakenSub (extendCtx (extendCtx Γ A) B) C) (wk2Sub Γ A B)

  /-- Substitute one expression for the newest variable. -/
  lf_def singleSub : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (arg : Tm Γ) ⇒ Sub Γ (extendCtx Γ A) :=
    fun Γ A arg => extendSub Γ Γ (idSub Γ) A arg

  /-- Simultaneous substitution for two newest variables. -/
  lf_def pairSub :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (arg1 : Tm Γ) ⇒ (arg2 : Tm Γ) ⇒ Sub Γ (extendCtx (extendCtx Γ A) B) :=
    fun Γ A B arg1 arg2 => extendSub Γ (extendCtx Γ A) (singleSub Γ A arg1) B arg2

  /-- Simultaneous substitution for three newest variables. -/
  lf_def tripleSub :
      (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
      (C : Ty (extendCtx (extendCtx Γ A) B)) ⇒ (arg1 : Tm Γ) ⇒ (arg2 : Tm Γ) ⇒
      (arg3 : Tm Γ) ⇒ Sub Γ (extendCtx (extendCtx (extendCtx Γ A) B) C) :=
    fun Γ A B C arg1 arg2 arg3 => extendSub Γ (extendCtx (extendCtx Γ A) B)
      (pairSub Γ A B arg1 arg2) C arg3

  /-- Reindex a type along an explicit substitution. -/
  lf_def reindexTy : (Γ : Ctx) ⇒ (Δ : Ctx) ⇒ (σ : Sub Γ Δ) ⇒ Ty Δ ⇒ Ty Γ :=
    fun Γ Δ σ A => substTy Γ Δ σ A

  /-- Reindex a term along an explicit substitution. -/
  lf_def reindexTm : (Γ : Ctx) ⇒ (Δ : Ctx) ⇒ (σ : Sub Γ Δ) ⇒ Tm Δ ⇒ Tm Γ :=
    fun Γ Δ σ t => substTm Γ Δ σ t
