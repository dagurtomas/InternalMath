/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.MLTT.Paths

/-!
# Contractibility, fibers, and equivalences in MLTT

The standard equivalence predicate over the separated `Ty`/`Tm` presentation.
-/

@[expose] public section

namespace MLTT

/-- Contractibility: a center together with paths from the center to every point. -/
internal def isContr : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ Ty Γ :=
  fun Γ A => sigmaTy Γ A (piTy (extendCtx Γ A) (weakenTy Γ A A) (idMotivePathTy Γ A))

/-- The fiber of `f : A → B` over `y : B`. -/
internal def fiber :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ (f : Tm Γ) ⇒ (y : Tm Γ) ⇒ Ty Γ :=
  fun Γ A B f y =>
    sigmaTy Γ A
      (idTy (extendCtx Γ A) (weakenTy Γ A B)
        (app (extendCtx Γ A) (weakenTy Γ A A)
          (weakenTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A B))
          (weakenTm Γ A f) (varTop Γ A))
        (weakenTm Γ A y))

/-- `isequiv(A,B,f)` as contractible fibers. -/
internal def isequiv :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ (f : Tm Γ) ⇒ Ty Γ :=
  fun Γ A B f =>
    piTy Γ B
      (isContr (extendCtx Γ B)
        (fiber (extendCtx Γ B) (weakenTy Γ B A) (weakenTy Γ B B)
          (weakenTm Γ B f) (varTop Γ B)))

/-- The type of equivalences `A ≃ B`. -/
internal def equivTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Ty Γ :=
  fun Γ A B =>
    sigmaTy Γ (arrowTy Γ A B)
      (isequiv (extendCtx Γ (arrowTy Γ A B))
        (weakenTy Γ (arrowTy Γ A B) A)
        (weakenTy Γ (arrowTy Γ A B) B)
        (varTop Γ (arrowTy Γ A B)))

end MLTT
