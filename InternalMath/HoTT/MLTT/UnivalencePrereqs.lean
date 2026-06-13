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
presentation.  Univalence uses Tarski-style universe codes: code terms are raw `Tm Γ` terms of
`univ Γ i`, and `elTy Γ i A` decodes a code to an ordinary type.
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

/-- The path component of the fiber of the identity function over `y`. -/
internal def idFiberPathTy :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Ty (extendCtx Γ A) :=
  fun Γ A y =>
    idTy (extendCtx Γ A) (weakenTy Γ A A)
      (app (extendCtx Γ A) (weakenTy Γ A A)
        (weakenTy (extendCtx Γ A) (weakenTy Γ A A) (weakenTy Γ A A))
        (weakenTm Γ A (idFun Γ A)) (varTop Γ A))
      (weakenTm Γ A y)

/-- The fiber type of the identity function over `y`. -/
internal def idFiberTy : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Ty Γ :=
  fun Γ A y => fiber Γ A A (idFun Γ A) y

/-- The center `(y, refl y)` of the identity-function fiber over `y`. -/
internal def idFiberCenter : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Tm Γ :=
  fun Γ A y => sigmaPair Γ A (idFiberPathTy Γ A y) y (refl Γ y)

/-- The path component of a reindexed identity-function fiber in context `Γ, p : fiber`. -/
internal def idFiberElimPathTy :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒
    Ty (extendCtx (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)) :=
  fun Γ A y =>
    idTy (extendCtx (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) A))
      (weakenTy (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) A) (weakenTy Γ (idFiberTy Γ A y) A))
      (app (extendCtx (extendCtx Γ (idFiberTy Γ A y))
          (weakenTy Γ (idFiberTy Γ A y) A))
        (weakenTy (extendCtx Γ (idFiberTy Γ A y))
          (weakenTy Γ (idFiberTy Γ A y) A) (weakenTy Γ (idFiberTy Γ A y) A))
        (weakenTy (extendCtx (extendCtx Γ (idFiberTy Γ A y))
            (weakenTy Γ (idFiberTy Γ A y) A))
          (weakenTy (extendCtx Γ (idFiberTy Γ A y))
            (weakenTy Γ (idFiberTy Γ A y) A) (weakenTy Γ (idFiberTy Γ A y) A))
          (weakenTy (extendCtx Γ (idFiberTy Γ A y))
            (weakenTy Γ (idFiberTy Γ A y) A) (weakenTy Γ (idFiberTy Γ A y) A)))
        (weakenTm (extendCtx Γ (idFiberTy Γ A y))
          (weakenTy Γ (idFiberTy Γ A y) A) (weakenTm Γ (idFiberTy Γ A y) (idFun Γ A)))
        (varTop (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)))
      (weakenTm (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) A) (weakenTm Γ (idFiberTy Γ A y) y))

/-- Motive for eliminating an arbitrary point of the identity-function fiber. -/
internal def idFiberElimMotive :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒
    Ty (extendCtx (extendCtx Γ (idFiberTy Γ A y))
      (sigmaTy (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)
        (idFiberElimPathTy Γ A y))) :=
  fun Γ A y =>
    idTy (extendCtx (extendCtx Γ (idFiberTy Γ A y))
      (sigmaTy (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)
        (idFiberElimPathTy Γ A y)))
      (weakenTy (extendCtx Γ (idFiberTy Γ A y))
        (sigmaTy (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)
          (idFiberElimPathTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) (idFiberTy Γ A y)))
      (weakenTm (extendCtx Γ (idFiberTy Γ A y))
        (sigmaTy (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)
          (idFiberElimPathTy Γ A y))
        (weakenTm Γ (idFiberTy Γ A y) (idFiberCenter Γ A y)))
      (varTop (extendCtx Γ (idFiberTy Γ A y))
        (sigmaTy (extendCtx Γ (idFiberTy Γ A y)) (weakenTy Γ (idFiberTy Γ A y) A)
          (idFiberElimPathTy Γ A y)))

/-- Branch for the Σ-induction contraction of the identity-function fiber. -/
internal def idFiberElimBranch :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒
    Tm (extendCtx (extendCtx (extendCtx Γ (idFiberTy Γ A y))
      (weakenTy Γ (idFiberTy Γ A y) A)) (idFiberElimPathTy Γ A y)) :=
  fun Γ A y =>
    refl (extendCtx (extendCtx (extendCtx Γ (idFiberTy Γ A y))
      (weakenTy Γ (idFiberTy Γ A y) A)) (idFiberElimPathTy Γ A y))
      (varTop (extendCtx (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) A)) (idFiberElimPathTy Γ A y))

/-- The contraction term for an arbitrary identity-function fiber element. -/
internal def idFiberContractionBody :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Tm (extendCtx Γ (idFiberTy Γ A y)) :=
  fun Γ A y =>
    sigmaInd (extendCtx Γ (idFiberTy Γ A y))
      (weakenTy Γ (idFiberTy Γ A y) A) (idFiberElimPathTy Γ A y)
      (idFiberElimMotive Γ A y) (idFiberElimBranch Γ A y) (varTop Γ (idFiberTy Γ A y))

/-- The contraction family centered at `(y, refl y)`. -/
internal def idFiberContraction :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Tm Γ :=
  fun Γ A y =>
    lam Γ (idFiberTy Γ A y)
      (idTy (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) (idFiberTy Γ A y))
        (weakenTm Γ (idFiberTy Γ A y) (idFiberCenter Γ A y))
        (varTop Γ (idFiberTy Γ A y)))
      (idFiberContractionBody Γ A y)

/-- Contractibility of identity-function fibers, constructible by path induction. -/
internal def idFiberContr :
    (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (y : Tm Γ) ⇒ Tm Γ :=
  fun Γ A y =>
    sigmaPair Γ (idFiberTy Γ A y)
      (piTy (extendCtx Γ (idFiberTy Γ A y))
        (weakenTy Γ (idFiberTy Γ A y) (idFiberTy Γ A y))
        (idMotivePathTy Γ (idFiberTy Γ A y)))
      (idFiberCenter Γ A y) (idFiberContraction Γ A y)

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

/-- The identity type between two universe codes. -/
internal def universePathTy :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Ty Γ :=
  fun Γ i A B => idTy Γ (univ Γ i) A B

/-- Motive for `idtoeqv`: path induction in a universe decodes endpoints to types. -/
internal def idtoeqvMotive : (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Ty (idMotiveCtx Γ (univ Γ i)) :=
  fun Γ i =>
    equivTy (idMotiveCtx Γ (univ Γ i))
      (elTy (idMotiveCtx Γ (univ Γ i)) i (idMotiveLeft Γ (univ Γ i)))
      (elTy (idMotiveCtx Γ (univ Γ i)) i (idMotiveRight Γ (univ Γ i)))

/-- Refl branch for `idtoeqv`, the identity equivalence on the decoded code. -/
internal def idtoeqvRefl : (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Tm (extendCtx Γ (univ Γ i)) :=
  fun Γ i =>
    idEquiv (extendCtx Γ (univ Γ i))
      (elTy (extendCtx Γ (univ Γ i)) i (varTop Γ (univ Γ i)))

/-- `idtoeqv` applied to one universe-equality proof. -/
internal def idtoeqvAt :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ (p : Tm Γ) ⇒ Tm Γ :=
  fun Γ i A B p => idInd Γ (univ Γ i) (idtoeqvMotive Γ i) (idtoeqvRefl Γ i) A B p

/-- The map from equality in the universe to equivalence, constructible by path induction. -/
internal def idtoeqv :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Tm Γ :=
  fun Γ i A B =>
    lam Γ (universePathTy Γ i A B)
      (weakenTy Γ (universePathTy Γ i A B) (equivTy Γ (elTy Γ i A) (elTy Γ i B)))
      (idtoeqvAt (extendCtx Γ (universePathTy Γ i A B)) i
        (weakenTm Γ (universePathTy Γ i A B) A)
        (weakenTm Γ (universePathTy Γ i A B) B)
        (varTop Γ (universePathTy Γ i A B)))

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
