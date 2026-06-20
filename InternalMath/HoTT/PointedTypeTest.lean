/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.HoTT

@[expose] public section

/-!
# Pointed types in HoTT and their extracted fragment

This file mirrors the active part of `../HoTTLean/test/pointed.lean` in the InternalLean HoTT
presentation.  The pointed-type API is defined as checked raw internal definitions in the full
`HoTT` theory, then `extract_theory_fragment` builds the minimal standalone fragment needed by the
final carrier-equivalence-to-carrier-path map.
-/

namespace HoTT

/-- Source of the univalence map. -/
internal def uaSource : (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Tm Γ ⇒ Tm Γ ⇒ Ty Γ :=
  fun Γ i A B => universePathTy Γ i A B

/-- Target of the univalence map. -/
internal def uaTarget : (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Tm Γ ⇒ Tm Γ ⇒ Ty Γ :=
  fun Γ i A B => equivTy Γ (elTy Γ i A) (elTy Γ i B)

/-- The fiber of `idtoeqv` over an equivalence. -/
internal def uaFiber :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Tm Γ ⇒ Ty Γ :=
  fun Γ i A B e => fiber Γ (uaSource Γ i A B) (uaTarget Γ i A B) (idtoeqv Γ i A B) e

/-- Contractibility of the `idtoeqv` fiber, supplied by univalence. -/
internal def uaFiberContr :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i A B e =>
    app Γ (uaTarget Γ i A B)
      (isContr (extendCtx Γ (uaTarget Γ i A B))
        (fiber (extendCtx Γ (uaTarget Γ i A B))
          (weakenTy Γ (uaTarget Γ i A B) (uaSource Γ i A B))
          (weakenTy Γ (uaTarget Γ i A B) (uaTarget Γ i A B))
          (weakenTm Γ (uaTarget Γ i A B) (idtoeqv Γ i A B))
          (varTop Γ (uaTarget Γ i A B))))
      (univalence Γ i A B) e

/-- The center of the `idtoeqv` fiber over an equivalence. -/
internal def uaFiberCenter :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i A B e => contrCenter Γ (uaFiber Γ i A B e) (uaFiberContr Γ i A B e)

/-- The equivalence-to-path map extracted from univalence. -/
internal def ua :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (A : Tm Γ) ⇒ (B : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i A B e =>
    sigmaFst Γ (uaSource Γ i A B)
      (idTy (extendCtx Γ (uaSource Γ i A B))
        (weakenTy Γ (uaSource Γ i A B) (uaTarget Γ i A B))
        (app (extendCtx Γ (uaSource Γ i A B))
          (weakenTy Γ (uaSource Γ i A B) (uaSource Γ i A B))
          (weakenTy (extendCtx Γ (uaSource Γ i A B))
            (weakenTy Γ (uaSource Γ i A B) (uaSource Γ i A B))
            (weakenTy Γ (uaSource Γ i A B) (uaTarget Γ i A B)))
          (weakenTm Γ (uaSource Γ i A B) (idtoeqv Γ i A B))
          (varTop Γ (uaSource Γ i A B)))
        (weakenTm Γ (uaSource Γ i A B) e))
      (uaFiberCenter Γ i A B e)

/-- Family assigning to a universe code its decoded point type. -/
internal def pointedTypePointFamily :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Ty (extendCtx Γ (univ Γ i)) :=
  fun Γ i => elTy (extendCtx Γ (univ Γ i)) i (varTop Γ (univ Γ i))

/-- A pointed type at universe level `i`: a universe code together with a point of its decoding. -/
internal def pointedType : (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Ty Γ :=
  fun Γ i => sigmaTy Γ (univ Γ i) (pointedTypePointFamily Γ i)

/-- Carrier code projection of a pointed type. -/
internal def pointedTypeCarrier :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i M => sigmaFst Γ (univ Γ i) (pointedTypePointFamily Γ i) M

/-- Motive used to project the chosen point of a pointed type. -/
internal def pointedTypePointMotive :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Ty (extendCtx Γ (pointedType Γ i)) :=
  fun Γ i =>
    elTy (extendCtx Γ (pointedType Γ i)) i
      (pointedTypeCarrier (extendCtx Γ (pointedType Γ i)) i
        (varTop Γ (pointedType Γ i)))

/-- Chosen-point projection of a pointed type. -/
internal def pointedTypePoint :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i M =>
    sigmaInd Γ (univ Γ i) (pointedTypePointFamily Γ i) (pointedTypePointMotive Γ i)
      (varTop (extendCtx Γ (univ Γ i)) (pointedTypePointFamily Γ i)) M

/-- Underlying function projection from an equivalence. -/
internal def equivFn : (Γ : Ctx) ⇒ (A : Ty Γ) ⇒ (B : Ty Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ A B e =>
    sigmaFst Γ (arrowTy Γ A B)
      (isequiv (extendCtx Γ (arrowTy Γ A B))
        (weakenTy Γ (arrowTy Γ A B) A)
        (weakenTy Γ (arrowTy Γ A B) B)
        (varTop Γ (arrowTy Γ A B))) e

/-- Type of equivalences between the carriers of two pointed types. -/
internal def pointedTypeCarrierEquivTy :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒ Ty Γ :=
  fun Γ i M N =>
    equivTy Γ (elTy Γ i (pointedTypeCarrier Γ i M))
      (elTy Γ i (pointedTypeCarrier Γ i N))

/-- Point-preservation equation for a carrier equivalence. -/
internal def pointedTypeEquivPointEqTy :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒
      Ty (extendCtx Γ (pointedTypeCarrierEquivTy Γ i M N)) :=
  fun Γ i M N =>
    idTy (extendCtx Γ (pointedTypeCarrierEquivTy Γ i M N))
      (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
        (elTy Γ i (pointedTypeCarrier Γ i N)))
      (app (extendCtx Γ (pointedTypeCarrierEquivTy Γ i M N))
        (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
          (elTy Γ i (pointedTypeCarrier Γ i M)))
        (weakenTy (extendCtx Γ (pointedTypeCarrierEquivTy Γ i M N))
          (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
            (elTy Γ i (pointedTypeCarrier Γ i M)))
          (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
            (elTy Γ i (pointedTypeCarrier Γ i N))))
        (equivFn (extendCtx Γ (pointedTypeCarrierEquivTy Γ i M N))
          (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
            (elTy Γ i (pointedTypeCarrier Γ i M)))
          (weakenTy Γ (pointedTypeCarrierEquivTy Γ i M N)
            (elTy Γ i (pointedTypeCarrier Γ i N)))
          (varTop Γ (pointedTypeCarrierEquivTy Γ i M N)))
        (weakenTm Γ (pointedTypeCarrierEquivTy Γ i M N) (pointedTypePoint Γ i M)))
      (weakenTm Γ (pointedTypeCarrierEquivTy Γ i M N) (pointedTypePoint Γ i N))

/-- Point-preserving equivalences of pointed types. -/
internal def pointedTypeEquiv :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒ Ty Γ :=
  fun Γ i M N =>
    sigmaTy Γ (pointedTypeCarrierEquivTy Γ i M N) (pointedTypeEquivPointEqTy Γ i M N)

/-- Carrier-equivalence projection from a pointed-type equivalence. -/
internal def pointedTypeEquivCarrierEquiv :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i M N e =>
    sigmaFst Γ (pointedTypeCarrierEquivTy Γ i M N) (pointedTypeEquivPointEqTy Γ i M N) e

/-- A point-preserving equivalence identifies the carrier universe codes. -/
internal def pointedTypeCarrierEq :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i M N e =>
    ua Γ i (pointedTypeCarrier Γ i M) (pointedTypeCarrier Γ i N)
      (pointedTypeEquivCarrierEquiv Γ i M N e)

/-- Profiling-style alias mirroring the HoTTLean test file. -/
internal def pointedTypeCarrierEq' :
    (Γ : Ctx) ⇒ (i : UnivLevel) ⇒ (M : Tm Γ) ⇒ (N : Tm Γ) ⇒ Tm Γ ⇒ Tm Γ :=
  fun Γ i M N e => pointedTypeCarrierEq Γ i M N e

/--
Typing for the univalence fiber contraction at the fiber selected by `e`.
This is admitted pending explicit-substitution computation for substituting the `isequiv` fiber
family at the newest variable.
-/
internal theorem uaFiberContr_isContr_ty
    (Γ : Ctx) (i : UnivLevel) (A : Tm Γ) (B : Tm Γ) (e : Tm Γ)
    (A_code : IsTm A (univ Γ i))
    (B_code : IsTm B (univ Γ i))
    (e_ty : IsTm e (uaTarget Γ i A B)) :
    IsTm (uaFiberContr Γ i A B e) (isContr Γ (uaFiber Γ i A B e)) := sorry

/-- The center selected from the univalence fiber contraction is a point of the fiber. -/
internal theorem uaFiberCenter_ty
    (Γ : Ctx) (i : UnivLevel) (A : Tm Γ) (B : Tm Γ) (e : Tm Γ)
    (A_code : IsTm A (univ Γ i))
    (B_code : IsTm B (univ Γ i))
    (e_ty : IsTm e (uaTarget Γ i A B)) :
    IsTm (uaFiberCenter Γ i A B e) (uaFiber Γ i A B e) := sorry

/-- The equivalence-to-path map produced from univalence is typed at the universe path type. -/
internal theorem ua_ty
    (Γ : Ctx) (i : UnivLevel) (A : Tm Γ) (B : Tm Γ) (e : Tm Γ)
    (A_code : IsTm A (univ Γ i))
    (B_code : IsTm B (univ Γ i))
    (e_ty : IsTm e (uaTarget Γ i A B)) :
    IsTm (ua Γ i A B e) (universePathTy Γ i A B) := sorry

/-- Carrier projection of a pointed type is a universe code. -/
internal theorem pointedTypeCarrier_ty
    (Γ : Ctx) (i : UnivLevel) (M : Tm Γ)
    (M_ty : IsTm M (pointedType Γ i)) :
    IsTm (pointedTypeCarrier Γ i M) (univ Γ i) := sorry

/-- Carrier-equivalence projection from a pointed equivalence is typed as a carrier equivalence. -/
internal theorem pointedTypeEquivCarrierEquiv_ty
    (Γ : Ctx) (i : UnivLevel) (M : Tm Γ) (N : Tm Γ) (e : Tm Γ)
    (e_ty : IsTm e (pointedTypeEquiv Γ i M N)) :
    IsTm (pointedTypeEquivCarrierEquiv Γ i M N e) (pointedTypeCarrierEquivTy Γ i M N) := sorry

/-- A point-preserving equivalence identifies the carrier universe codes. -/
internal theorem pointedTypeCarrierEq'_ty
    (Γ : Ctx) (i : UnivLevel) (M : Tm Γ) (N : Tm Γ) (e : Tm Γ)
    (M_ty : IsTm M (pointedType Γ i))
    (N_ty : IsTm N (pointedType Γ i))
    (e_ty : IsTm e (pointedTypeEquiv Γ i M N)) :
    IsTm (pointedTypeCarrierEq' Γ i M N e)
      (universePathTy Γ i (pointedTypeCarrier Γ i M) (pointedTypeCarrier Γ i N)) := sorry

end HoTT

/-!
## Extracted minimal fragment

The listed roots are the public definitions of this test.  Fragment extraction pulls in exactly
the HoTT declarations needed by these roots and their checked internal dependencies; the fragment is
not manually redeclared.  The typing theorem above is explicit admitted debt for now, so it is not
an extraction root.
-/

extract_theory_fragment PointedTypeHoTT from HoTT for pointedType pointedTypeCarrier
  pointedTypePoint pointedTypeEquiv pointedTypeCarrierEq'

generate_model_interface PointedTypeHoTT as PointedTypeHoTTModel

namespace PointedTypeHoTT

/--
A placeholder model of the extracted pointed-type fragment, with every primitive field left as a
Lean `sorry`.
-/
def sorryModel : PointedTypeHoTTModel where
  Ctx := sorry
  Ty := sorry
  Tm := sorry
  Sub := sorry
  UnivLevel := sorry
  extendCtx := sorry
  weakenSub := sorry
  substTy := sorry
  substTm := sorry
  varTop := sorry
  idTy := sorry
  refl := sorry
  idInd := sorry
  piTy := sorry
  lam := sorry
  app := sorry
  sigmaTy := sorry
  sigmaPair := sorry
  sigmaInd := sorry
  univ := sorry
  elTy := sorry
  univalence := sorry

end PointedTypeHoTT
