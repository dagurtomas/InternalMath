/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Derived

/-!
# MLTT path operations

Standard path operations over intensional MLTT, stated against the separated `Ty`/`Tm` syntax.
Definitions in this file are raw MLTT terms/types.  Typing theorems for these raw terms are a later
layer.
-/

@[expose] public section

namespace MLTT

/-- Projection from the identity-eliminator motive context to its base context. -/
internal def idMotiveBaseSub :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Sub (idMotiveCtx Γ A) Γ :=
  fun Γ A => wk3Sub Γ A (weakenTy Γ A A) (idMotivePathTy Γ A)

/-- The left endpoint type in the identity-eliminator motive context. -/
internal def idMotiveEndpointTy :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty (idMotiveCtx Γ A) :=
  fun Γ A =>
    weakenTy (extendCtx (extendCtx Γ A) (weakenTy Γ A A)) (idMotivePathTy Γ A)
      (weakenTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A A))

/-- The left endpoint in the identity-eliminator motive context. -/
internal def idMotiveLeft : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (idMotiveCtx Γ A) :=
  fun Γ A => prev2Var Γ A (weakenTy Γ A A) (idMotivePathTy Γ A)

/-- The right endpoint in the identity-eliminator motive context. -/
internal def idMotiveRight : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (idMotiveCtx Γ A) :=
  fun Γ A => prevVar (extendCtx Γ A) (weakenTy Γ A A) (idMotivePathTy Γ A)

/-- Motive for path inverse. -/
internal def pathInvMotive : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty (idMotiveCtx Γ A) :=
  fun Γ A => idTy (idMotiveCtx Γ A) (idMotiveEndpointTy Γ A)
    (idMotiveRight Γ A) (idMotiveLeft Γ A)

/-- Refl branch for path inverse. -/
internal def pathInvRefl : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (extendCtx Γ A) :=
  fun Γ A => refl (extendCtx Γ A) (varTop Γ A)

/-- Path inverse, constructible by identity induction. -/
internal def pathInv :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ Tm Γ :=
  fun Γ A x y p => idInd Γ A (pathInvMotive Γ A) (pathInvRefl Γ A) x y p

/-- Projection from the identity-eliminator motive context to its left endpoint context. -/
internal def idMotiveLeftSub :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Sub (idMotiveCtx Γ A) (extendCtx Γ A) :=
  fun Γ A =>
    compSub (idMotiveCtx Γ A) (extendCtx (extendCtx Γ A) (weakenTy Γ A A))
      (extendCtx Γ A)
      (weakenSub (extendCtx (extendCtx Γ A) (weakenTy Γ A A)) (idMotivePathTy Γ A))
      (weakenSub (extendCtx Γ A) (weakenTy Γ A A))

/-- Projection from the identity-eliminator motive context to its right endpoint context. -/
internal def idMotiveRightSub :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Sub (idMotiveCtx Γ A) (extendCtx Γ A) :=
  fun Γ A =>
    extendSub (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A (idMotiveRight Γ A)

/-- Motive for transport along an identity proof. -/
internal def transportMotive :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒ Ty (idMotiveCtx Γ A) :=
  fun Γ A C =>
    arrowTy (idMotiveCtx Γ A)
      (substTy (idMotiveCtx Γ A) (extendCtx Γ A) (idMotiveLeftSub Γ A) C)
      (substTy (idMotiveCtx Γ A) (extendCtx Γ A) (idMotiveRightSub Γ A) C)

/-- Refl branch for transport: the identity map on the fiber. -/
internal def transportRefl :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒ Tm (extendCtx Γ A) :=
  fun Γ A C =>
    lam (extendCtx Γ A) C (weakenTy (extendCtx Γ A) C C) (varTop (extendCtx Γ A) C)

/-- Transport as a function between fibers of a dependent family. -/
internal def transportFn :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ Tm Γ :=
  fun Γ A C x y p => idInd Γ A (transportMotive Γ A C) (transportRefl Γ A C) x y p

/-- Transport of an element along a path in the base. -/
internal def transport :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ (u : Tm Γ) ⇒ Tm Γ :=
  fun Γ A C x y p u =>
    app Γ (substTopTy Γ A C x)
      (weakenTy Γ (substTopTy Γ A C x) (substTopTy Γ A C y))
      (transportFn Γ A C x y p) u

/-- Motive family used to define path composition via transport. -/
internal def pathCompMotive :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (x : Tm Γ) ⇒ Ty (extendCtx Γ A) :=
  fun Γ A x => idTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTm Γ A x) (varTop Γ A)

/-- Path composition, constructible as transport in the family `λ z, x = z`. -/
internal def pathComp :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (z : Tm Γ) ⇒
    (p : Tm Γ) ⇒ (q : Tm Γ) ⇒ Tm Γ :=
  fun Γ A x y z p q => transport Γ A (pathCompMotive Γ A x) y z q p

/-- Motive for non-dependent action on paths. -/
internal def apMotive :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ (f : Tm Γ) ⇒ Ty (idMotiveCtx Γ A) :=
  fun Γ A B f =>
    idTy (idMotiveCtx Γ A) (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) B)
      (app (idMotiveCtx Γ A)
        (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)
        (weakenTy (idMotiveCtx Γ A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) B))
        (substTm (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) f)
        (idMotiveLeft Γ A))
      (app (idMotiveCtx Γ A)
        (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)
        (weakenTy (idMotiveCtx Γ A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) B))
        (substTm (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) f)
        (idMotiveRight Γ A))

/-- Refl branch for non-dependent action on paths. -/
internal def apRefl :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ (f : Tm Γ) ⇒ Tm (extendCtx Γ A) :=
  fun Γ A B f =>
    refl (extendCtx Γ A)
      (app (extendCtx Γ A) (weakenTy Γ A A)
        (weakenTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A B))
        (weakenTm Γ A f) (varTop Γ A))

/-- Non-dependent action on paths, constructible by identity induction. -/
internal def ap :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ (f : Tm Γ) ⇒
    (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ Tm Γ :=
  fun Γ A B f x y p => idInd Γ A (apMotive Γ A B f) (apRefl Γ A B f) x y p

/-- Dependent-path type `u =^C_p v`, defined using transport and identity. -/
internal def depPathTy :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ (u : Tm Γ) ⇒ (v : Tm Γ) ⇒ Ty Γ :=
  fun Γ A C x y p u v => idTy Γ (substTopTy Γ A C y) (transport Γ A C x y p u) v

/-- The path variable in the identity-eliminator motive context. -/
internal def idMotivePathTerm : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm (idMotiveCtx Γ A) :=
  fun Γ A => varTop (extendCtx (extendCtx Γ A) (weakenTy Γ A A)) (idMotivePathTy Γ A)

/-- Substitution used to reindex a dependent family to the `apd` motive context. -/
internal def apdPointSub :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Sub (extendCtx (idMotiveCtx Γ A)
      (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)) (extendCtx Γ A) :=
  fun Γ A =>
    extendSub
      (extendCtx (idMotiveCtx Γ A)
        (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A))
      Γ
      (compSub
        (extendCtx (idMotiveCtx Γ A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A))
        (idMotiveCtx Γ A) Γ
        (weakenSub (idMotiveCtx Γ A)
          (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A))
        (idMotiveBaseSub Γ A))
      A
      (varTop (idMotiveCtx Γ A)
        (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A))

/-- The dependent family reindexed to the `apd` motive context. -/
internal def apdMotiveFamily :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    Ty (extendCtx (idMotiveCtx Γ A)
      (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)) :=
  fun Γ A C =>
    substTy
      (extendCtx (idMotiveCtx Γ A)
        (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A))
      (extendCtx Γ A) (apdPointSub Γ A) C

/-- Motive for dependent action on paths. -/
internal def apdMotive :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (body : Tm (extendCtx Γ A)) ⇒ Ty (idMotiveCtx Γ A) :=
  fun Γ A C body =>
    depPathTy (idMotiveCtx Γ A)
      (substTy (idMotiveCtx Γ A) Γ (idMotiveBaseSub Γ A) A)
      (apdMotiveFamily Γ A C)
      (idMotiveLeft Γ A) (idMotiveRight Γ A) (idMotivePathTerm Γ A)
      (substTm (idMotiveCtx Γ A) (extendCtx Γ A) (idMotiveLeftSub Γ A) body)
      (substTm (idMotiveCtx Γ A) (extendCtx Γ A) (idMotiveRightSub Γ A) body)

/-- Refl branch for dependent action on paths. -/
internal def apdRefl :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (body : Tm (extendCtx Γ A)) ⇒ Tm (extendCtx Γ A) :=
  fun Γ A C body => refl (extendCtx Γ A) body

/-- Dependent action on paths, constructible by identity induction. -/
internal def apd :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (C : Ty (extendCtx Γ A)) ⇒
    (body : Tm (extendCtx Γ A)) ⇒ (x : Tm Γ) ⇒ (y : Tm Γ) ⇒ (p : Tm Γ) ⇒ Tm Γ :=
  fun Γ A C body x y p => idInd Γ A (apdMotive Γ A C body) (apdRefl Γ A C body) x y p

end MLTT
