/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalLean.Command

/-!
# Simply typed lambda calculus

A small intrinsic InternalLean specification of simply typed lambda calculus, with separate
contexts and types, explicit substitutions, finite product and function types, intrinsically typed
terms, and β/η/congruence rules for typed term conversion.

The theory is designed for the Curry--Howard--Lambek experiment in `Model.lean`: it is strong
enough to interpret any cartesian closed category, and it includes context-representability data so
arbitrary contexts can be compared with morphisms out of a single representing object in the
syntactic cartesian closed category.
-/

@[expose] public section

/--
An intrinsic presentation of simply typed lambda calculus.

Contexts and types are separate syntactic classes.  Terms are indexed by a context and a type, so
there is no separate term-typing judgment.  Substitutions are explicit, making the usual
substitution metatheory available to models and to the syntactic category construction.  The
judgment `EqTm Γ A t u` records typed definitional equality/conversion between parallel terms.
-/
declare_type_theory LambdaCalculus where

  /-- Basic syntax for contexts, types, terms, and substitutions. -/
  model_section Syntax

  /-- Contexts of typed variables. -/
  syntax_sort Ctx
  syntax_sort_role Ctx : context

  /-- Simple types. -/
  syntax_sort Ty
  syntax_sort_role Ty : type_sort

  /-- Intrinsically typed terms in a context. -/
  syntax_sort Tm (Γ : Ctx) (A : Ty)
  syntax_sort_role Tm : term_sort

  /-- Explicit substitutions from one context to another. -/
  syntax_sort Sub (Γ : Ctx) (Δ : Ctx)

  /-- The terminal/unit type. -/
  lf_opaque unitTy : Ty

  /-- Binary product type former. -/
  lf_opaque prodTy (A : Ty) (B : Ty) : Ty

  /-- Function type former. -/
  lf_opaque arrowTy (A : Ty) (B : Ty) : Ty

  /-- Empty context. -/
  lf_opaque emptyCtx : Ctx

  /-- Context extension by one variable. -/
  lf_opaque extendCtx (Γ : Ctx) (A : Ty) : Ctx

  /-- Identity substitution. -/
  lf_opaque idSub (Γ : Ctx) : Sub Γ Γ

  /-- Composition of substitutions. -/
  lf_opaque compSub (Γ : Ctx) (Δ : Ctx) (Θ : Ctx)
    (σ : Sub Γ Δ) (τ : Sub Δ Θ) : Sub Γ Θ

  /-- The unique substitution to the empty context. -/
  lf_opaque emptySub (Γ : Ctx) : Sub Γ emptyCtx

  /-- Projection from an extended context to its base. -/
  lf_opaque weakenSub (Γ : Ctx) (A : Ty) : Sub (extendCtx Γ A) Γ

  /-- Extension of a substitution by one term. -/
  lf_opaque extendSub (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ : Sub Γ Δ) (t : Tm Γ A) : Sub Γ (extendCtx Δ A)

  /-- Reindex a term along a substitution. -/
  lf_opaque substTm (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ : Sub Γ Δ) (t : Tm Δ A) : Tm Γ A

  /-- The newest variable in an extended context. -/
  lf_opaque varZero (Γ : Ctx) (A : Ty) : Tm (extendCtx Γ A) A

  /-- Weakening of a term along context extension, derived as reindexing along `weakenSub`. -/
  lf_def weakenTm : (Γ : Ctx) ⇒ (A : Ty) ⇒ (B : Ty) ⇒ Tm Γ A ⇒
      Tm (extendCtx Γ B) A :=
    fun Γ A B t => substTm (extendCtx Γ B) Γ A (weakenSub Γ B) t

  /-- Introduction term for the unit type. -/
  lf_opaque unitIntro (Γ : Ctx) : Tm Γ unitTy

  /-- Pairing for product types. -/
  lf_opaque pairTm (Γ : Ctx) (A : Ty) (B : Ty)
    (fst : Tm Γ A) (snd : Tm Γ B) : Tm Γ (prodTy A B)

  /-- First projection from a product type. -/
  lf_opaque fstTm (Γ : Ctx) (A : Ty) (B : Ty) (pair : Tm Γ (prodTy A B)) : Tm Γ A

  /-- Second projection from a product type. -/
  lf_opaque sndTm (Γ : Ctx) (A : Ty) (B : Ty) (pair : Tm Γ (prodTy A B)) : Tm Γ B

  /-- Lambda abstraction. -/
  lf_opaque lam (Γ : Ctx) (A : Ty) (B : Ty) (body : Tm (extendCtx Γ A) B) :
    Tm Γ (arrowTy A B)

  /-- Function application. -/
  lf_opaque app (Γ : Ctx) (A : Ty) (B : Ty)
    (fn : Tm Γ (arrowTy A B)) (arg : Tm Γ A) : Tm Γ B

  /-- Substitute a term for the newest variable of a term in an extended context. -/
  lf_def substTop : (Γ : Ctx) ⇒ (A : Ty) ⇒ (B : Ty) ⇒
      Tm (extendCtx Γ A) B ⇒ Tm Γ A ⇒ Tm Γ B :=
    fun Γ A B body arg =>
      substTm Γ (extendCtx Γ A) B (extendSub Γ Γ A (idSub Γ) arg) body

  /-- A type representing a context as a single product-coded variable. -/
  lf_opaque ctxObj (Γ : Ctx) : Ty

  /-- The substitution from a context to its singleton representing context. -/
  lf_opaque ctxToSingleton (Γ : Ctx) : Sub Γ (extendCtx emptyCtx (ctxObj Γ))

  /-- The substitution from a singleton representing context back to the represented context. -/
  lf_opaque ctxFromSingleton (Γ : Ctx) : Sub (extendCtx emptyCtx (ctxObj Γ)) Γ

  /-- One-variable composition, derived as explicit substitution into a singleton context. -/
  lf_def homComp : (A : Ty) ⇒ (B : Ty) ⇒ (C : Ty) ⇒
      Tm (extendCtx emptyCtx A) B ⇒ Tm (extendCtx emptyCtx B) C ⇒
        Tm (extendCtx emptyCtx A) C :=
    fun A B C f g =>
      substTm (extendCtx emptyCtx A) (extendCtx emptyCtx B) C
        (extendSub (extendCtx emptyCtx A) emptyCtx B (emptySub (extendCtx emptyCtx A)) f) g

  /-- Typed definitional equality/conversion of terms. -/
  judgment EqTm (Γ : Ctx) (A : Ty) (t : Tm Γ A) (u : Tm Γ A)
  judgment_role EqTm : term_conversion

  /-- Definitional equality/conversion of substitutions. -/
  judgment EqSub (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ)

  /-- Equivalence rules for typed term and substitution conversion. -/
  model_section Equality

  /-- Reflexivity of typed term conversion. -/
  rule eq_refl (Γ : Ctx) (A : Ty) (t : Tm Γ A) where
    conclusion : EqTm Γ A t t

  /-- Symmetry of typed term conversion. -/
  rule eq_symm (Γ : Ctx) (A : Ty) (t : Tm Γ A) (u : Tm Γ A) where
    premise h : EqTm Γ A t u
    conclusion : EqTm Γ A u t

  /-- Transitivity of typed term conversion. -/
  rule eq_trans (Γ : Ctx) (A : Ty) (t : Tm Γ A) (u : Tm Γ A) (v : Tm Γ A) where
    premise left : EqTm Γ A t u
    premise right : EqTm Γ A u v
    conclusion : EqTm Γ A t v

  /-- Reflexivity of substitution conversion. -/
  rule eqSub_refl (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) where
    conclusion : EqSub Γ Δ σ σ

  /-- Symmetry of substitution conversion. -/
  rule eqSub_symm (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ) where
    premise h : EqSub Γ Δ σ τ
    conclusion : EqSub Γ Δ τ σ

  /-- Transitivity of substitution conversion. -/
  rule eqSub_trans (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ) (υ : Sub Γ Δ) where
    premise left : EqSub Γ Δ σ τ
    premise right : EqSub Γ Δ τ υ
    conclusion : EqSub Γ Δ σ υ

  /-- Category and comprehension laws for substitutions. -/
  model_section Substitution

  /-- Left identity law for substitution composition. -/
  rule compSub_id_left (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) where
    conclusion : EqSub Γ Δ (compSub Γ Γ Δ (idSub Γ) σ) σ

  /-- Right identity law for substitution composition. -/
  rule compSub_id_right (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) where
    conclusion : EqSub Γ Δ (compSub Γ Δ Δ σ (idSub Δ)) σ

  /-- Associativity law for substitution composition. -/
  rule compSub_assoc (Γ : Ctx) (Δ : Ctx) (Θ : Ctx) (Ξ : Ctx)
    (σ : Sub Γ Δ) (τ : Sub Δ Θ) (υ : Sub Θ Ξ) where
    conclusion : EqSub Γ Ξ
      (compSub Γ Θ Ξ (compSub Γ Δ Θ σ τ) υ)
      (compSub Γ Δ Ξ σ (compSub Δ Θ Ξ τ υ))

  /-- Congruence for substitution composition. -/
  rule compSub_congr (Γ : Ctx) (Δ : Ctx) (Θ : Ctx)
    (σ₁ : Sub Γ Δ) (σ₂ : Sub Γ Δ) (τ₁ : Sub Δ Θ) (τ₂ : Sub Δ Θ) where
    premise left : EqSub Γ Δ σ₁ σ₂
    premise right : EqSub Δ Θ τ₁ τ₂
    conclusion : EqSub Γ Θ (compSub Γ Δ Θ σ₁ τ₁) (compSub Γ Δ Θ σ₂ τ₂)

  /-- Every substitution to the empty context is definitionally equal to `emptySub`. -/
  rule emptySub_eta (Γ : Ctx) (σ : Sub Γ emptyCtx) where
    conclusion : EqSub Γ emptyCtx σ (emptySub Γ)

  /-- The base projection of an extended substitution is the original substitution. -/
  rule extendSub_weaken (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ : Sub Γ Δ) (t : Tm Γ A) where
    conclusion : EqSub Γ Δ
      (compSub Γ (extendCtx Δ A) Δ (extendSub Γ Δ A σ t) (weakenSub Δ A)) σ

  /-- The newest variable reindexed along an extended substitution is the extending term. -/
  rule extendSub_varZero (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ : Sub Γ Δ) (t : Tm Γ A) where
    conclusion : EqTm Γ A
      (substTm Γ (extendCtx Δ A) A (extendSub Γ Δ A σ t) (varZero Δ A)) t

  /-- Eta law for substitutions into an extended context. -/
  rule extendSub_eta (Γ : Ctx) (Δ : Ctx) (A : Ty) (σ : Sub Γ (extendCtx Δ A)) where
    conclusion : EqSub Γ (extendCtx Δ A) σ
      (extendSub Γ Δ A
        (compSub Γ (extendCtx Δ A) Δ σ (weakenSub Δ A))
        (substTm Γ (extendCtx Δ A) A σ (varZero Δ A)))

  /-- Congruence for substitution extension. -/
  rule extendSub_congr (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ₁ : Sub Γ Δ) (σ₂ : Sub Γ Δ) (t₁ : Tm Γ A) (t₂ : Tm Γ A) where
    premise sub_eq : EqSub Γ Δ σ₁ σ₂
    premise term_eq : EqTm Γ A t₁ t₂
    conclusion : EqSub Γ (extendCtx Δ A)
      (extendSub Γ Δ A σ₁ t₁) (extendSub Γ Δ A σ₂ t₂)

  /-- Context representation is a section/retraction, first direction. -/
  rule ctxToFrom (Γ : Ctx) where
    conclusion : EqSub Γ Γ
      (compSub Γ (extendCtx emptyCtx (ctxObj Γ)) Γ
        (ctxToSingleton Γ) (ctxFromSingleton Γ))
      (idSub Γ)

  /-- Context representation is a section/retraction, second direction. -/
  rule ctxFromTo (Γ : Ctx) where
    conclusion : EqSub (extendCtx emptyCtx (ctxObj Γ)) (extendCtx emptyCtx (ctxObj Γ))
      (compSub (extendCtx emptyCtx (ctxObj Γ)) Γ (extendCtx emptyCtx (ctxObj Γ))
        (ctxFromSingleton Γ) (ctxToSingleton Γ))
      (idSub (extendCtx emptyCtx (ctxObj Γ)))

  /-- Reindexing along the identity substitution is the identity operation. -/
  rule subst_id (Γ : Ctx) (A : Ty) (t : Tm Γ A) where
    conclusion : EqTm Γ A (substTm Γ Γ A (idSub Γ) t) t

  /-- Reindexing along a composite substitution is iterated reindexing. -/
  rule subst_comp (Γ : Ctx) (Δ : Ctx) (Θ : Ctx) (A : Ty)
    (σ : Sub Γ Δ) (τ : Sub Δ Θ) (t : Tm Θ A) where
    conclusion : EqTm Γ A
      (substTm Γ Θ A (compSub Γ Δ Θ σ τ) t)
      (substTm Γ Δ A σ (substTm Δ Θ A τ t))

  /-- Congruence for term reindexing. -/
  rule subst_congr (Γ : Ctx) (Δ : Ctx) (A : Ty)
    (σ₁ : Sub Γ Δ) (σ₂ : Sub Γ Δ) (t₁ : Tm Δ A) (t₂ : Tm Δ A) where
    premise sub_eq : EqSub Γ Δ σ₁ σ₂
    premise term_eq : EqTm Δ A t₁ t₂
    conclusion : EqTm Γ A (substTm Γ Δ A σ₁ t₁) (substTm Γ Δ A σ₂ t₂)

  /-- Substitution preserves the unit introduction term. -/
  rule subst_unit (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) where
    conclusion : EqTm Γ unitTy (substTm Γ Δ unitTy σ (unitIntro Δ)) (unitIntro Γ)

  /-- Substitution preserves product pairing. -/
  rule subst_pair (Γ : Ctx) (Δ : Ctx) (A : Ty) (B : Ty)
    (σ : Sub Γ Δ) (fst : Tm Δ A) (snd : Tm Δ B) where
    conclusion : EqTm Γ (prodTy A B)
      (substTm Γ Δ (prodTy A B) σ (pairTm Δ A B fst snd))
      (pairTm Γ A B (substTm Γ Δ A σ fst) (substTm Γ Δ B σ snd))

  /-- Substitution preserves first projections. -/
  rule subst_fst (Γ : Ctx) (Δ : Ctx) (A : Ty) (B : Ty)
    (σ : Sub Γ Δ) (pair : Tm Δ (prodTy A B)) where
    conclusion : EqTm Γ A
      (substTm Γ Δ A σ (fstTm Δ A B pair))
      (fstTm Γ A B (substTm Γ Δ (prodTy A B) σ pair))

  /-- Substitution preserves second projections. -/
  rule subst_snd (Γ : Ctx) (Δ : Ctx) (A : Ty) (B : Ty)
    (σ : Sub Γ Δ) (pair : Tm Δ (prodTy A B)) where
    conclusion : EqTm Γ B
      (substTm Γ Δ B σ (sndTm Δ A B pair))
      (sndTm Γ A B (substTm Γ Δ (prodTy A B) σ pair))

  /-- Substitution preserves lambda abstraction by extending the substitution under the binder. -/
  rule subst_lam (Γ : Ctx) (Δ : Ctx) (A : Ty) (B : Ty)
    (σ : Sub Γ Δ) (body : Tm (extendCtx Δ A) B) where
    conclusion : EqTm Γ (arrowTy A B)
      (substTm Γ Δ (arrowTy A B) σ (lam Δ A B body))
      (lam Γ A B
        (substTm (extendCtx Γ A) (extendCtx Δ A) B
          (extendSub (extendCtx Γ A) Δ A
            (compSub (extendCtx Γ A) Γ Δ (weakenSub Γ A) σ)
            (varZero Γ A))
          body))

  /-- Substitution preserves function application. -/
  rule subst_app (Γ : Ctx) (Δ : Ctx) (A : Ty) (B : Ty)
    (σ : Sub Γ Δ) (fn : Tm Δ (arrowTy A B)) (arg : Tm Δ A) where
    conclusion : EqTm Γ B
      (substTm Γ Δ B σ (app Δ A B fn arg))
      (app Γ A B
        (substTm Γ Δ (arrowTy A B) σ fn)
        (substTm Γ Δ A σ arg))

  /-- β/η and congruence rules for products. -/
  model_section Products

  /-- First projection β-rule for products. -/
  rule prod_beta_fst (Γ : Ctx) (A : Ty) (B : Ty) (fst : Tm Γ A) (snd : Tm Γ B) where
    conclusion : EqTm Γ A (fstTm Γ A B (pairTm Γ A B fst snd)) fst

  /-- Second projection β-rule for products. -/
  rule prod_beta_snd (Γ : Ctx) (A : Ty) (B : Ty) (fst : Tm Γ A) (snd : Tm Γ B) where
    conclusion : EqTm Γ B (sndTm Γ A B (pairTm Γ A B fst snd)) snd

  /-- Product η-rule. -/
  rule prod_eta (Γ : Ctx) (A : Ty) (B : Ty) (pair : Tm Γ (prodTy A B)) where
    conclusion : EqTm Γ (prodTy A B) pair
      (pairTm Γ A B (fstTm Γ A B pair) (sndTm Γ A B pair))

  /-- Congruence for product pairing. -/
  rule pair_congr (Γ : Ctx) (A : Ty) (B : Ty)
    (fst₁ : Tm Γ A) (fst₂ : Tm Γ A) (snd₁ : Tm Γ B) (snd₂ : Tm Γ B) where
    premise fst_eq : EqTm Γ A fst₁ fst₂
    premise snd_eq : EqTm Γ B snd₁ snd₂
    conclusion : EqTm Γ (prodTy A B)
      (pairTm Γ A B fst₁ snd₁) (pairTm Γ A B fst₂ snd₂)

  /-- Congruence for the first product projection. -/
  rule fst_congr (Γ : Ctx) (A : Ty) (B : Ty)
    (pair₁ : Tm Γ (prodTy A B)) (pair₂ : Tm Γ (prodTy A B)) where
    premise pair_eq : EqTm Γ (prodTy A B) pair₁ pair₂
    conclusion : EqTm Γ A (fstTm Γ A B pair₁) (fstTm Γ A B pair₂)

  /-- Congruence for the second product projection. -/
  rule snd_congr (Γ : Ctx) (A : Ty) (B : Ty)
    (pair₁ : Tm Γ (prodTy A B)) (pair₂ : Tm Γ (prodTy A B)) where
    premise pair_eq : EqTm Γ (prodTy A B) pair₁ pair₂
    conclusion : EqTm Γ B (sndTm Γ A B pair₁) (sndTm Γ A B pair₂)

  /-- β/η and congruence rules for functions and unit. -/
  model_section FunctionsAndUnit

  /-- β-rule for lambda abstraction and application. -/
  rule beta (Γ : Ctx) (A : Ty) (B : Ty)
    (body : Tm (extendCtx Γ A) B) (arg : Tm Γ A) where
    conclusion : EqTm Γ B (app Γ A B (lam Γ A B body) arg) (substTop Γ A B body arg)

  /-- η-rule for function types. -/
  rule eta (Γ : Ctx) (A : Ty) (B : Ty) (fn : Tm Γ (arrowTy A B)) where
    conclusion : EqTm Γ (arrowTy A B) fn
      (lam Γ A B
        (app (extendCtx Γ A) A B
          (weakenTm Γ (arrowTy A B) A fn)
          (varZero Γ A)))

  /-- Congruence for lambda abstraction. -/
  rule lam_congr (Γ : Ctx) (A : Ty) (B : Ty)
    (body₁ : Tm (extendCtx Γ A) B) (body₂ : Tm (extendCtx Γ A) B) where
    premise body_eq : EqTm (extendCtx Γ A) B body₁ body₂
    conclusion : EqTm Γ (arrowTy A B) (lam Γ A B body₁) (lam Γ A B body₂)

  /-- Congruence for function application. -/
  rule app_congr (Γ : Ctx) (A : Ty) (B : Ty)
    (fn₁ : Tm Γ (arrowTy A B)) (fn₂ : Tm Γ (arrowTy A B))
    (arg₁ : Tm Γ A) (arg₂ : Tm Γ A) where
    premise fn_eq : EqTm Γ (arrowTy A B) fn₁ fn₂
    premise arg_eq : EqTm Γ A arg₁ arg₂
    conclusion : EqTm Γ B (app Γ A B fn₁ arg₁) (app Γ A B fn₂ arg₂)

  /-- Any two unit terms are definitionally equal. -/
  rule unit_eta (Γ : Ctx) (t : Tm Γ unitTy) where
    conclusion : EqTm Γ unitTy t (unitIntro Γ)
