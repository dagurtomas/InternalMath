/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalLean.Command

/-!
# Basic MLTT syntax and judgments

The reusable base signature for the HoTT-book MLTT development.  It contains only the three core
syntax families and the four basic judgments:

* context well-formedness, `IsCtx Γ`;
* type formation, `IsTy A`, read `Γ ⊢ A type`;
* term typing, `IsTm a A`, read `Γ ⊢ a : A`;
* judgmental equality of terms, `EqTm a b A`, read `Γ ⊢ a ≡ b : A`.

Object-theory structural operations and type formers live in extension theories.
-/

@[expose] public section

/-- Basic MLTT syntax and judgments, before structural operations and type formers. -/
declare_type_theory MLTT.Basic where

  model_section Judgments

  /-- Contexts. -/
  syntax_sort Ctx
  syntax_sort_role Ctx : context

  /-- Types in a context. -/
  syntax_sort Ty (Γ : Ctx)
  syntax_sort_role Ty : type_sort

  /-- Raw terms in a context.  Their type is supplied by `IsTm`. -/
  syntax_sort Tm (Γ : Ctx)
  syntax_sort_role Tm : term_sort

  /-- Context well-formedness: `Γ ctx`. -/
  judgment IsCtx (Γ : Ctx)
  judgment_role IsCtx : context_wellformedness

  /-- Type formation: `Γ ⊢ A type`. -/
  judgment IsTy {Γ : Ctx} (A : Ty Γ)
  judgment_role IsTy : type_formation

  /-- Term typing: `Γ ⊢ a : A`. -/
  judgment IsTm {Γ : Ctx} (a : Tm Γ) (A : Ty Γ)
  judgment_role IsTm : term_typing

  /-- Judgmental equality: `Γ ⊢ a ≡ b : A`. -/
  judgment EqTm {Γ : Ctx} (a : Tm Γ) (b : Tm Γ) (A : Ty Γ)
  judgment_role EqTm : term_conversion
