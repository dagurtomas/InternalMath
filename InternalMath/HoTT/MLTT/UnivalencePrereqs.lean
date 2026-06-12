/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Equivalences

/-!
# MLTT prerequisites for function extensionality and univalence

Prerequisite constructions for the HoTT layer, stated against the separated `Ty`/`Tm` MLTT
presentation.  Universe-code details for univalence are left as explicit internal debt while the
core refactor settles.
-/

@[expose] public section

namespace MLTT

/-- Identity function on a type. -/
internal def idFun : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm Γ :=
  fun Γ A => lam Γ A (weakenTy Γ A A) (varTop Γ A)

/-- The codomain `Π x:A, f x = g x` of `happly_{f,g}`. -/
internal def happlyCodTy :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty Γ :=
  fun Γ A B f g =>
    piTy Γ A
      (idTy (extendCtx Γ A) B
        (app (extendCtx Γ A) (weakenTy Γ A A)
          (weakenTy (extendCtx Γ A) (weakenTy Γ A A) B)
          (weakenTm Γ A f) (varTop Γ A))
        (app (extendCtx Γ A) (weakenTy Γ A A)
          (weakenTy (extendCtx Γ A) (weakenTy Γ A A) B)
          (weakenTm Γ A g) (varTop Γ A)))

/-- Contractibility of identity-function fibers, constructible by path induction. -/
internal def idFiberContr :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Tm Γ :=
  sorry

/-- The identity function is an equivalence, constructible from `idFiberContr`. -/
internal def idIsEquiv : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm Γ :=
  fun Γ A =>
    lam Γ A
      (isContr (extendCtx Γ A)
        (fiber (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A A)
          (weakenTm Γ A (idFun Γ A)) (varTop Γ A)))
      (idFiberContr (extendCtx Γ A) (weakenTy Γ A A) (varTop Γ A))

/-- The identity equivalence on a type. -/
internal def idEquiv : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Tm Γ :=
  fun Γ A =>
    sigmaPair Γ (arrowTy Γ A A)
      (isequiv (extendCtx Γ (arrowTy Γ A A))
        (weakenTy Γ (arrowTy Γ A A) A) (weakenTy Γ (arrowTy Γ A A) A)
        (varTop Γ (arrowTy Γ A A)))
      (idFun Γ A) (idIsEquiv Γ A)

/-- The identity type between two types regarded as elements of universe `i`.

In the separated `Ty`/`Tm` presentation this records the book's `A =_{𝒰ᵢ} B` type without adding a
separate type-equality judgment.  It is admitted until universe coding for separated type syntax is
made explicit. -/
internal def universePathTy :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Ty Γ :=
  sorry

/-- The map from equality in the universe to equivalence, constructible by path induction. -/
internal def idtoeqv :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Tm Γ :=
  sorry

/-- The equality type between dependent functions, used as the source of `happly`. -/
internal def happlySource :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty Γ :=
  fun Γ A B f g => idTy Γ (piTy Γ A B) f g

/-- Context obtained by adding a function-equality proof. -/
internal def happlyPathCtx :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ctx :=
  fun Γ A B f g => extendCtx Γ (happlySource Γ A B f g)

/-- The domain type weakened to the `happly` path context. -/
internal def happlyPathA :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty (happlyPathCtx Γ A B f g) :=
  fun Γ A B f g => weakenTy Γ (happlySource Γ A B f g) A

/-- Context with both the function equality and a point of the domain. -/
internal def happlyPointCtx :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ctx :=
  fun Γ A B f g => extendCtx (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g)

/-- Projection from the `happly` point context back to the base context. -/
internal def happlyPointToBase :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Sub (happlyPointCtx Γ A B f g) Γ :=
  fun Γ A B f g =>
    compSub (happlyPointCtx Γ A B f g) (happlyPathCtx Γ A B f g) Γ
      (weakenSub (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g))
      (weakenSub Γ (happlySource Γ A B f g))

/-- Substitution picking out the point variable in the `happly` point context. -/
internal def happlyPointSub :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Sub (happlyPointCtx Γ A B f g) (extendCtx Γ A) :=
  fun Γ A B f g =>
    extendSub (happlyPointCtx Γ A B f g) Γ (happlyPointToBase Γ A B f g) A
      (varTop (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g))

/-- The dependent codomain reindexed to the `happly` point context. -/
internal def happlyPointB :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty (happlyPointCtx Γ A B f g) :=
  fun Γ A B f g =>
    substTy (happlyPointCtx Γ A B f g) (extendCtx Γ A) (happlyPointSub Γ A B f g) B

/-- The application-domain type in the `happly` point context. -/
internal def happlyAppDomain :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty (happlyPointCtx Γ A B f g) :=
  fun Γ A B f g =>
    weakenTy (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g)
      (happlyPathA Γ A B f g)

/-- The left-hand pointwise application used in the refl branch for `happly`. -/
internal def happlyLeftApp :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Tm (happlyPointCtx Γ A B f g) :=
  fun Γ A B f g =>
    app (happlyPointCtx Γ A B f g) (happlyAppDomain Γ A B f g)
      (weakenTy (happlyPointCtx Γ A B f g) (happlyAppDomain Γ A B f g)
        (happlyPointB Γ A B f g))
      (weakenTm (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g)
        (weakenTm Γ (happlySource Γ A B f g) f))
      (varTop (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g))

/-- The pointwise equality type used in the refl branch for `happly`. -/
internal def happlyPointEq :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Ty (happlyPointCtx Γ A B f g) :=
  fun Γ A B f g =>
    idTy (happlyPointCtx Γ A B f g) (happlyPointB Γ A B f g)
      (happlyLeftApp Γ A B f g) (happlyLeftApp Γ A B f g)

/-- Pointwise action of equality between dependent functions, constructible by path induction. -/
internal def happly :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty (extendCtx Γ A)) ⇒
    (f : Tm Γ) ⇒ (g : Tm Γ) ⇒ Tm Γ :=
  fun Γ A B f g =>
    lam Γ (happlySource Γ A B f g)
      (weakenTy Γ (happlySource Γ A B f g) (happlyCodTy Γ A B f g))
      (lam (happlyPathCtx Γ A B f g) (happlyPathA Γ A B f g)
        (happlyPointEq Γ A B f g)
        (refl (happlyPointCtx Γ A B f g) (happlyLeftApp Γ A B f g)))

end MLTT
