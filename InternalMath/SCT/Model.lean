/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# SCT model file

This file contains the generated SCT model interface and a quasicategory/Kan-complex model
skeleton. The concrete top-level carriers record the intended quasicategory semantics while the
full model is developed.

The current pass fills the small amount of structure that is already directly available from
mathlib: Kan complexes embed in quasicategories, `Δ[0]` is a Kan complex, identities and
composition are the ordinary maps in the full subcategory of quasicategories, and binary products of
quasicategories are quasicategories. The remaining `sorry`s are genuine semantic gaps in the
current mathlib/SCT interface: natural isomorphisms are equivalence edges in functor
quasicategories, pullbacks should be homotopy/∞-categorical pullbacks, and the fibration/universe
fields require the universal cocartesian fibration and directed-univalence machinery.

For functor quasicategories and natural isomorphisms, this file now includes a local skeleton for
API that is being developed in the `emilyriehl/infinity-cosmos` project and mathlib PR #35287. The
skeleton uses the existing simplicial internal hom, assumes/sorries quasicategory closure, and
models natural isomorphisms as invertible/equivalence edges in those functor quasicategories.
-/

@[expose] public section

generate_model_interface SCT as SCTModel

open SCT CategoryTheory
open Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet

universe u

/-- Quasicategories are invariant under isomorphism of simplicial sets. -/
public lemma Quasicategory.ofIso {X Y : SSet.{u}} (e : X ≅ Y) [Quasicategory Y] :
    Quasicategory X where
  hornFilling' := by
    intro n i σ₀ h0 hn
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (S := Y) (σ₀ ≫ e.hom) h0 hn
    use σ ≫ e.inv
    simpa [Category.assoc] using congrArg (fun f => f ≫ e.inv) hσ

/-- Every standard simplex is a quasicategory, via its identification with a finite-ordinal
nerve. -/
public instance stdSimplex.quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) :=
  Quasicategory.ofIso (stdSimplex.isoNerve n)

end SSet

namespace SCTModelHelpers

universe u

/-- The terminal simplicial set is a Kan complex.

The proof uses the Quillen fibration structure on simplicial sets: the map from `Δ[0]` to the
chosen terminal simplicial set is an isomorphism because `Δ[0]` is terminal, hence it has the right
lifting property against the horn inclusions.
-/
lemma kanComplexStdSimplexZero : SSet.KanComplex (Δ[0] : SSet.{u}) := by
  rw [SSet.KanComplex]
  rw [HomotopicalAlgebra.isFibrant_iff]
  rw [SSet.modelCategoryQuillen.fibration_iff]
  haveI : IsIso (Limits.terminal.from (Δ[0] : SSet.{u})) :=
    Limits.isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ Limits.terminalIsTerminal _
  exact MorphismProperty.rlp_of_isIso SSet.modelCategoryQuillen.J _

/-- Products of quasicategories are quasicategories.

This is the pointwise product argument: an inner horn in `X × Y` is the same as compatible inner
horns in `X` and `Y`, and the two fillers combine by the cartesian product of simplicial sets.
-/
lemma quasicategoryTensor (X Y : SSet.{u}) [SSet.Quasicategory X] [SSet.Quasicategory Y] :
    SSet.Quasicategory (X ⊗ Y) where
  hornFilling' := by
    intro n i σ₀ h0 hn
    let fstXY := SemiCartesianMonoidalCategory.fst X Y
    let sndXY := SemiCartesianMonoidalCategory.snd X Y
    obtain ⟨σX, hX⟩ :=
      SSet.Quasicategory.hornFilling' (S := X) (σ₀ ≫ fstXY) h0 hn
    obtain ⟨σY, hY⟩ :=
      SSet.Quasicategory.hornFilling' (S := Y) (σ₀ ≫ sndXY) h0 hn
    let σ : Δ[n + 2] ⟶ X ⊗ Y := CartesianMonoidalCategory.lift σX σY
    use σ
    ext m z <;> simp [σ, fstXY, sndXY, hX, hY]

/-- Bundle the nerve of an ordinary category as a quasicategory. -/
public def qcatNerve (C : Type u) [Category.{u} C] : SSet.QCat.{u} :=
  ⟨CategoryTheory.nerve C, inferInstance⟩

/-- Bundle the map on nerves induced by an ordinary functor. -/
public def qcatNerveMap {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    qcatNerve C ⟶ qcatNerve D :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (CategoryTheory.nerveMap F)

/-- Interpret an anima, bundled as a Kan complex, as its underlying quasicategory. -/
def animaCat (A : ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)) :
    SSet.QCat.{u} := by
  letI : SSet.KanComplex A.obj := A.property
  exact ⟨A.obj, inferInstance⟩

/-- The terminal anima is `Δ[0]`. -/
def terminalAnima : ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S) :=
  ⟨Δ[0], kanComplexStdSimplexZero⟩

/-- The unique map from a quasicategory to the terminal anima. -/
def terminalProjection (C : SSet.QCat.{u}) : C ⟶ animaCat terminalAnima :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))

/-- The initial quasicategory, realized as the nerve of the empty category. -/
def initialQCat : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} Empty)

/-- The unique map from the initial quasicategory to any quasicategory. -/
def initialMap (C : SSet.QCat.{u}) : initialQCat ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    { app := fun Δ => TypeCat.ofHom fun x => False.elim (by
        exact x.obj ⟨0, by simp⟩ |>.down.elim)
      naturality := by
        intro Δ Γ f
        ext x
        exact False.elim (by exact x.obj ⟨0, by simp⟩ |>.down.elim) }

/-- The walking arrow, modeled as the nerve of the linearly ordered category with two objects. -/
def intervalQCat : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} (Fin 2))

/-- A vertex of the walking arrow as a map from `Δ[0]`. -/
def intervalVertex (i : Fin 2) : animaCat terminalAnima ⟶ intervalQCat :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SSet.yonedaEquiv.symm (CategoryTheory.ComposableArrows.mk₀ (ULift.up i)))

/-- Pullback-indexing shape for cospans, modeled by the ordinary walking cospan nerve. -/
public def pullbackShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingCospan)

/-- Pushout-indexing shape for spans, modeled by the ordinary walking span nerve. -/
public def pushoutShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingSpan)

/-- Binary product of bundled quasicategories, using the cartesian product of simplicial sets. -/
def qcatProduct (C D : SSet.QCat.{u}) : SSet.QCat.{u} := by
  letI : SSet.Quasicategory C.obj := C.property
  letI : SSet.Quasicategory D.obj := D.property
  exact ⟨C.obj ⊗ D.obj, quasicategoryTensor C.obj D.obj⟩

/-- First projection from the product quasicategory. -/
def qcatProdPr1 (C D : SSet.QCat.{u}) : qcatProduct C D ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.fst C.obj D.obj)

/-- Second projection from the product quasicategory. -/
def qcatProdPr2 (C D : SSet.QCat.{u}) : qcatProduct C D ⟶ D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.snd C.obj D.obj)

/-- Pairing into the product quasicategory. -/
def qcatProdPair (T C D : SSet.QCat.{u}) (F : T ⟶ C) (G : T ⟶ D) :
    T ⟶ qcatProduct C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (CartesianMonoidalCategory.lift F.hom G.hom)

section UpstreamFunctorQuasicategorySkeleton

/-!
## Upstream functor-quasicategory skeleton

This section is a temporary adapter for functor quasicategories, equivalence edges, natural
isomorphisms, and the associated curry/uncurry API. It follows the route used in
`emilyriehl/infinity-cosmos` and mathlib PR #35287: functor objects are simplicial internal homs,
natural transformations are edges in those internal homs, and natural isomorphisms are
invertible/equivalence edges.

The `sorry`s in this section mark upstream API assumptions, not local project proof obligations.
Contributors should not spend effort closing these local `sorry`s directly unless they are replacing
this adapter by the corresponding mathlib/infinity-cosmos definitions and theorems. In particular,
the cartesian-closedness theorem for quasicategories and the compatibility results for equivalence
edges should come from upstream once that material lands in mathlib.
-/

/-- The cartesian symmetry map for the pointwise product of simplicial sets. -/
def swapTensor (X Y : SSet.{u}) : X ⊗ Y ⟶ Y ⊗ X :=
  CartesianMonoidalCategory.lift
    (SemiCartesianMonoidalCategory.snd X Y)
    (SemiCartesianMonoidalCategory.fst X Y)

/-- Assumption/API target: the simplicial internal hom `D^C` is a quasicategory when `C` and `D`
are quasicategories.

This is the cartesian-closedness theorem for quasicategories. It is expected to be replaced by the
mathlib/infinity-cosmos API once available.
-/
lemma quasicategoryInternalHom (C D : SSet.QCat.{u}) :
    SSet.Quasicategory ((ihom C.obj).obj D.obj) := by
  sorry

/-- The functor quasicategory `Fun(C,D)`, realized as the simplicial internal hom. -/
def funCat (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨(ihom C.obj).obj D.obj, quasicategoryInternalHom C D⟩

/-- A strict functor `C ⟶ D` as a vertex of the functor quasicategory `Fun(C,D)`. -/
def functorVertex (C D : SSet.QCat.{u}) (F : C ⟶ D) : (funCat C D).obj _⦋0⦌ :=
  SSet.unitHomEquiv (funCat C D).obj
    (MonoidalClosed.curry ((ρ_ C.obj).hom ≫ F.hom))

/-- Natural transformations are edges in the functor quasicategory. -/
abbrev NatTrans (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  SSet.Edge (functorVertex C D F) (functorVertex C D G)

/-- Invertible/equivalence-edge data for an edge in a simplicial set.

This mirrors the `Edge.IsIso`/`Edge.InvStruct` API from `emilyriehl/infinity-cosmos` and mathlib
PR #35287: an inverse edge together with two `2`-simplices witnessing the two composites as
identity edges. In a quasicategory this is one standard presentation of an equivalence edge.
-/
structure EdgeIsIso {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : SSet.Edge x₀ x₁) : Type u where
  inv : SSet.Edge x₁ x₀
  homInvId : SSet.Edge.CompStruct e inv (SSet.Edge.id x₀)
  invHomId : SSet.Edge.CompStruct inv e (SSet.Edge.id x₁)

namespace EdgeIsIso

/-- The identity edge is invertible. -/
def id {X : SSet.{u}} (x : X _⦋0⦌) : EdgeIsIso (SSet.Edge.id x) where
  inv := SSet.Edge.id x
  homInvId := SSet.Edge.CompStruct.idComp (SSet.Edge.id x)
  invHomId := SSet.Edge.CompStruct.idComp (SSet.Edge.id x)

/-- Invertibility is symmetric. -/
def symm {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {e : SSet.Edge x₀ x₁}
    (I : EdgeIsIso e) : EdgeIsIso I.inv where
  inv := e
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- Simplicial maps preserve invertible edges. -/
def map {X Y : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {e : SSet.Edge x₀ x₁}
    (I : EdgeIsIso e) (f : X ⟶ Y) : EdgeIsIso (e.map f) where
  inv := I.inv.map f
  homInvId := by simpa using I.homInvId.map f
  invHomId := by simpa using I.invHomId.map f

end EdgeIsIso

/-- Natural-isomorphism data in the model: an edge in `Fun(C,D)` which is an equivalence edge. -/
abbrev NatIso (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  (α : NatTrans C D F G) × EdgeIsIso α

/-- The identity natural isomorphism. -/
def idNatIso (C D : SSet.QCat.{u}) (F : C ⟶ D) : NatIso C D F F :=
  ⟨SSet.Edge.id (functorVertex C D F), EdgeIsIso.id _⟩

/-- Transport a natural isomorphism across equality of strict functors. -/
def natIsoOfEq {C D : SSet.QCat.{u}} {F G : C ⟶ D} (h : F = G) : NatIso C D F G := by
  subst h
  exact idNatIso C D F

/-- Assumption/API target: compose natural transformations as edges in the functor
quasicategory. -/
def compNatTrans {C D : SSet.QCat.{u}} {F G H : C ⟶ D}
    (α : NatTrans C D F G) (β : NatTrans C D G H) : NatTrans C D F H := by
  sorry

/-- Assumption/API target: equivalence edges in a quasicategory are closed under composition. -/
def compEdgeIsIso {C D : SSet.QCat.{u}} {F G H : C ⟶ D}
    {α : NatTrans C D F G} {β : NatTrans C D G H}
    (hα : EdgeIsIso α) (hβ : EdgeIsIso β) : EdgeIsIso (compNatTrans α β) := by
  sorry

/-- Vertical composition of natural isomorphisms. -/
def compNatIso (C D : SSet.QCat.{u}) {F G H : C ⟶ D}
    (α : NatIso C D F G) (β : NatIso C D G H) : NatIso C D F H :=
  ⟨compNatTrans α.1 β.1, compEdgeIsIso α.2 β.2⟩

/-- Inverse of a natural isomorphism. -/
def invNatIso (C D : SSet.QCat.{u}) {F G : C ⟶ D}
    (α : NatIso C D F G) : NatIso C D G F :=
  ⟨α.2.inv, α.2.symm⟩

/-- Assumption/API target: pre-whiskering preserves equivalence edges in functor
quasicategories, with the expected endpoint compatibility. -/
def preWhiskerNatIso (B C D : SSet.QCat.{u}) (K : B ⟶ C) {F G : C ⟶ D}
    (α : NatIso C D F G) : NatIso B D (K ≫ F) (K ≫ G) := by
  sorry

/-- Assumption/API target: post-whiskering preserves equivalence edges in functor
quasicategories, with the expected endpoint compatibility. -/
def postWhiskerNatIso (B C D : SSet.QCat.{u}) {F G : B ⟶ C} (K : C ⟶ D)
    (α : NatIso B C F G) : NatIso B D (F ≫ K) (G ≫ K) := by
  sorry

/-- Horizontal composition of natural isomorphisms. -/
def horizCompNatIso (B C D : SSet.QCat.{u}) {F G : B ⟶ C} {H K : C ⟶ D}
    (α : NatIso B C F G) (β : NatIso C D H K) : NatIso B D (F ≫ H) (G ≫ K) := by
  sorry

/-- Equivalence of quasicategories as forward/backward functors with natural-isomorphism unit and
counit. Once the upstream equivalence-edge API is available, this package should become routine
structure built from `NatIso`.
-/
structure CatEquivData (C D : SSet.QCat.{u}) : Type u where
  forward : C ⟶ D
  backward : D ⟶ C
  unitIso : NatIso C C (forward ≫ backward) (𝟙 C)
  counitIso : NatIso D D (backward ≫ forward) (𝟙 D)

/-- Precomposition as a functor between functor quasicategories. -/
def precompFunctor (A B C : SSet.QCat.{u}) (F : A ⟶ B) : funCat B C ⟶ funCat A C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) ((MonoidalClosed.pre F.hom).app C.obj)

/-- Postcomposition as a functor between functor quasicategories. -/
def postcompFunctor (A B C : SSet.QCat.{u}) (F : B ⟶ C) : funCat A B ⟶ funCat A C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) ((ihom A.obj).map F.hom)

/-- Evaluation `Fun(C,D) × C ⟶ D`. -/
def evalFunctor (C D : SSet.QCat.{u}) : qcatProduct (funCat C D) C ⟶ D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (swapTensor (funCat C D).obj C.obj ≫ (ihom.ev C.obj).app D.obj)

/-- Currying for maps `Γ × C ⟶ D`. -/
def curryFunctor (Γ C D : SSet.QCat.{u}) (F : qcatProduct Γ C ⟶ D) : Γ ⟶ funCat C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (MonoidalClosed.curry (swapTensor C.obj Γ.obj ≫ F.hom))

/-- Uncurrying for maps `Γ ⟶ Fun(C,D)`. -/
def uncurryFunctor (Γ C D : SSet.QCat.{u})
    (F : Γ ⟶ funCat C D) : qcatProduct Γ C ⟶ D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (swapTensor Γ.obj C.obj ≫ MonoidalClosed.uncurry F.hom)

/-- Assumption/API target: currying followed by uncurrying agrees up to natural isomorphism. -/
def curryBeta (Γ C D : SSet.QCat.{u}) (F : qcatProduct Γ C ⟶ D) :
    NatIso (qcatProduct Γ C) D (uncurryFunctor Γ C D (curryFunctor Γ C D F)) F := by
  sorry

/-- Assumption/API target: uncurrying followed by currying agrees up to natural isomorphism. -/
def curryEta (Γ C D : SSet.QCat.{u}) (F : Γ ⟶ funCat C D) :
    NatIso Γ (funCat C D) (curryFunctor Γ C D (uncurryFunctor Γ C D F)) F := by
  sorry

/-- Assumption/API target: currying preserves natural isomorphisms. -/
def curryNatIso (Γ C D : SSet.QCat.{u}) {F G : qcatProduct Γ C ⟶ D}
    (α : NatIso (qcatProduct Γ C) D F G) :
    NatIso Γ (funCat C D) (curryFunctor Γ C D F) (curryFunctor Γ C D G) := by
  sorry

/-- Assumption/API target: uncurrying preserves natural isomorphisms. -/
def uncurryNatIso (Γ C D : SSet.QCat.{u}) {F G : Γ ⟶ funCat C D}
    (α : NatIso Γ (funCat C D) F G) :
    NatIso (qcatProduct Γ C) D (uncurryFunctor Γ C D F) (uncurryFunctor Γ C D G) := by
  sorry

/-- Assumption/API target: the forward functor in the curry/uncurry equivalence. -/
def curryUncurryForward (Γ C D : SSet.QCat.{u}) :
    funCat Γ (funCat C D) ⟶ funCat (qcatProduct Γ C) D := by
  sorry

/-- Assumption/API target: the backward functor in the curry/uncurry equivalence. -/
def curryUncurryBackward (Γ C D : SSet.QCat.{u}) :
    funCat (qcatProduct Γ C) D ⟶ funCat Γ (funCat C D) := by
  sorry

/-- Assumption/API target: the unit for the curry/uncurry equivalence. -/
def curryUncurryUnit (Γ C D : SSet.QCat.{u}) :
    NatIso (funCat Γ (funCat C D)) (funCat Γ (funCat C D))
      (curryUncurryForward Γ C D ≫ curryUncurryBackward Γ C D) (𝟙 _) := by
  sorry

/-- Assumption/API target: the counit for the curry/uncurry equivalence. -/
def curryUncurryCounit (Γ C D : SSet.QCat.{u}) :
    NatIso (funCat (qcatProduct Γ C) D) (funCat (qcatProduct Γ C) D)
      (curryUncurryBackward Γ C D ≫ curryUncurryForward Γ C D) (𝟙 _) := by
  sorry

/-- The source vertex of the walking-arrow quasicategory. -/
def intervalZeroSimplex : intervalQCat.{u}.obj _⦋0⦌ :=
  CategoryTheory.ComposableArrows.mk₀ (ULift.up (0 : Fin 2))

/-- The target vertex of the walking-arrow quasicategory. -/
def intervalOneSimplex : intervalQCat.{u}.obj _⦋0⦌ :=
  CategoryTheory.ComposableArrows.mk₀ (ULift.up (1 : Fin 2))

/-- The nondegenerate edge in the walking-arrow quasicategory. -/
def intervalEdge : SSet.Edge intervalZeroSimplex.{u} intervalOneSimplex.{u} where
  edge := CategoryTheory.ComposableArrows.mk₁
    (CategoryTheory.homOfLE
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 by decide))
  src_eq := CategoryTheory.ComposableArrows.ext₀ rfl
  tgt_eq := CategoryTheory.ComposableArrows.ext₀ rfl

/-- The edge of `C` represented by an interval-shaped functor `Δ[1] ⟶ C`. -/
def intervalFunctorEdge (C : SSet.QCat.{u}) (f : intervalQCat ⟶ C) :
    SSet.Edge (f.hom.app _ intervalZeroSimplex) (f.hom.app _ intervalOneSimplex) :=
  intervalEdge.map f.hom

/-- Invertible interval-shaped morphisms are represented by invertible edges in the target
quasicategory. -/
abbrev InvertibleMorphismData (C : SSet.QCat.{u}) (f : intervalQCat ⟶ C) : Type u :=
  EdgeIsIso (intervalFunctorEdge C f)

end UpstreamFunctorQuasicategorySkeleton

end SCTModelHelpers

def sctModel.{u} : SCTModel.{u} where
  Anima := ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)
  SCat := SSet.QCat.{u}
  Functor C D := C ⟶ D
  NatTrans := SCTModelHelpers.NatTrans
  /- This is equivalence-edge data in `Fun(C,D)`. The objectwise interpretation is the theorem
  supplied by `objectwiseNatIsoComponent` below. -/
  ObjectwiseNatIsoData := fun _ _ _ _ α => SCTModelHelpers.EdgeIsIso α
  CatEquiv := SCTModelHelpers.CatEquivData
  AnimaIndexedCat := sorry
  InvertibleMorphismData := SCTModelHelpers.InvertibleMorphismData
  GroupoidWitness := fun C => ULift.{u} (PLift (SSet.KanComplex C.obj))
  ExponentiableFunctor := sorry
  ContextCat := sorry
  ContextFunctor := sorry
  ContextNatIso := sorry
  ContextCatEquiv := sorry
  ContextPullbackSquare := sorry
  GroupoidalContext := sorry
  ContextMorphismCollection := sorry
  ContextObjectCollection := sorry
  IsofibrationWitness := sorry
  Adjunction := sorry
  LeftAdjointSection := sorry
  RightAdjointSection := sorry
  LeftFibrationWitness := sorry
  RightFibrationWitness := sorry
  LocallyCocartesianFibrationWitness := sorry
  LocallyCartesianFibrationWitness := sorry
  CartesianFunctorWitness := sorry
  FiberwiseInitialWitness := sorry
  FiberwiseTerminalWitness := sorry
  ContextFibration := sorry
  ContextCartesianFibrationWitness := sorry
  ContextCocartesianFibrationWitness := sorry
  LimitCone := sorry
  ColimitCocone := sorry
  HasLimitsOfShape := sorry
  HasColimitsOfShape := sorry
  DirectedUnivalenceWitness := sorry
  UniverseWitness := sorry
  SmallWitness := sorry
  SmallCocartesianFibrationWitness := sorry
  SmallFibersWitness := sorry
  RegularUniverseWitness := sorry
  ExponentiableFibrationWitness := sorry
  ConstructiveRegularUniverseWitness := sorry
  animaCat := SCTModelHelpers.animaCat
  mapAnima := sorry
  sigmaAnimaIndexed := sorry
  sigmaAnimaIndexedProjection := sorry
  idFunctor := fun C => 𝟙 C
  compFunctor := fun _ _ _ F G => F ≫ G
  idNatIso := SCTModelHelpers.idNatIso
  compNatIso := fun C D _ _ _ α β => SCTModelHelpers.compNatIso C D α β
  invNatIso := fun C D _ _ α => SCTModelHelpers.invNatIso C D α
  leftUnitor := fun _ _ _ => SCTModelHelpers.natIsoOfEq (by simp)
  rightUnitor := fun _ _ _ => SCTModelHelpers.natIsoOfEq (by simp)
  assocFunctor := fun _ _ _ _ _ _ _ => SCTModelHelpers.natIsoOfEq (by simp [Category.assoc])
  preWhiskerNatIso := fun B C D K _ _ α => SCTModelHelpers.preWhiskerNatIso B C D K α
  postWhiskerNatIso := fun B C D _ _ K α => SCTModelHelpers.postWhiskerNatIso B C D K α
  horizCompNatIso := fun B C D _ _ _ _ α β => SCTModelHelpers.horizCompNatIso B C D α β
  catEquivOfData := fun _ _ F G η ε => ⟨F, G, η, ε⟩
  catEquivForward := fun _ _ e => e.forward
  catEquivBackward := fun _ _ e => e.backward
  catEquivUnit := fun _ _ e => e.unitIso
  catEquivCounit := fun _ _ e => e.counitIso
  terminalAnima := SCTModelHelpers.terminalAnima
  terminalProjection := SCTModelHelpers.terminalProjection
  terminalUnique := fun _ _ _ => SCTModelHelpers.natIsoOfEq (by
    apply ObjectProperty.hom_ext
    exact SSet.stdSimplex.ext₀)
  initialCat := SCTModelHelpers.initialQCat
  initialElim := SCTModelHelpers.initialMap
  initialUnique := fun _ _ _ => SCTModelHelpers.natIsoOfEq (by
    apply ObjectProperty.hom_ext
    ext n x
    exact False.elim (x.obj ⟨0, by simp⟩).down.elim)
  initialStrict := sorry
  prodCat := SCTModelHelpers.qcatProduct
  prodPr1 := SCTModelHelpers.qcatProdPr1
  prodPr2 := SCTModelHelpers.qcatProdPr2
  prodPair := SCTModelHelpers.qcatProdPair
  prodBeta1 := fun _ _ _ _ _ => SCTModelHelpers.natIsoOfEq (by
    ext n x
    rfl)
  prodBeta2 := fun _ _ _ _ _ => SCTModelHelpers.natIsoOfEq (by
    ext n x
    rfl)
  prodEta := fun _ _ _ _ => SCTModelHelpers.natIsoOfEq (by
    ext n x
    rfl)
  prodUniq := sorry
  /- Missing: coproduct closure for quasicategories should use the disjoint union of simplicial
  sets together with the fact that inner horns are connected. This is not currently packaged in
  mathlib. -/
  coprodCat := sorry
  coprodIn1 := sorry
  coprodIn2 := sorry
  coprodCase := sorry
  coprodBeta1 := sorry
  coprodBeta2 := sorry
  coprodEta := sorry
  coprodUniq := sorry
  /- Missing: the SCT pullback should be a homotopy/∞-categorical pullback in `Cat_∞`.
  Strict pullbacks of simplicial sets along arbitrary maps do not supply this field. -/
  pullbackCat := sorry
  pullbackPr1 := sorry
  pullbackPr2 := sorry
  pullbackComm := sorry
  pullbackLift := sorry
  pullbackBeta1 := sorry
  pullbackBeta2 := sorry
  pullbackUniq := sorry
  pullbackEta := sorry
  coprodBaseChangeForward := sorry
  coprodBaseChangeBackward := sorry
  coprodBaseChangeUnit := sorry
  coprodBaseChangeCounit := sorry
  coprodDisjointForward := sorry
  coprodDisjointBackward := sorry
  coprodDisjointUnit := sorry
  coprodDisjointCounit := sorry
  funCat := SCTModelHelpers.funCat
  precompFunctor := SCTModelHelpers.precompFunctor
  postcompFunctor := SCTModelHelpers.postcompFunctor
  evalFunctor := SCTModelHelpers.evalFunctor
  curryFunctor := SCTModelHelpers.curryFunctor
  uncurryFunctor := SCTModelHelpers.uncurryFunctor
  curryBeta := SCTModelHelpers.curryBeta
  curryEta := SCTModelHelpers.curryEta
  curryNatIso := fun Γ C D _ _ α => SCTModelHelpers.curryNatIso Γ C D α
  uncurryNatIso := fun Γ C D _ _ α => SCTModelHelpers.uncurryNatIso Γ C D α
  curryUncurryForward := SCTModelHelpers.curryUncurryForward
  curryUncurryBackward := SCTModelHelpers.curryUncurryBackward
  curryUncurryUnit := SCTModelHelpers.curryUncurryUnit
  curryUncurryCounit := SCTModelHelpers.curryUncurryCounit
  intervalCat := SCTModelHelpers.intervalQCat
  intervalZero := SCTModelHelpers.intervalVertex 0
  intervalOne := SCTModelHelpers.intervalVertex 1
  /- Missing: the low-dimensional face, degeneracy, and endpoint universal-property data below
  should be transported from the usual simplex maps. -/
  simplex2Id0 := sorry
  simplex2Can := sorry
  simplex2Id1 := sorry
  simplex2Face01 := sorry
  simplex2Face12 := sorry
  simplex2Face02 := sorry
  simplex2Deg0 := sorry
  simplex2Deg1 := sorry
  simplex2Face01Zero := sorry
  simplex2Face01One := sorry
  simplex2Face12Zero := sorry
  simplex2Face12One := sorry
  simplex2Face02Zero := sorry
  simplex2Face02One := sorry
  simplex2Deg0Beta := sorry
  simplex2Deg1Beta := sorry
  functorObjectSourceCompat := sorry
  functorObjectTargetCompat := sorry
  natTransObject := sorry
  horizCompIdId := sorry
  horizCompCompComp := sorry
  horizCompLeftId := sorry
  horizCompRightId := sorry
  assocFunctorNaturality := sorry
  squareLowerTriangle := sorry
  squareUpperTriangle := sorry
  squareRestriction := sorry
  squareExtension := sorry
  squareRestrictionUnit := sorry
  squareRestrictionCounit := sorry
  segalRestriction := sorry
  segalExtension := sorry
  segalUnit := sorry
  segalCounit := sorry
  compositeSourceCompat := sorry
  compositeTargetCompat := sorry
  composeLeftUnit := sorry
  composeRightUnit := sorry
  composeAssoc := sorry
  invertibleMorphismInverse := sorry
  invertibleMorphismInverseSource := sorry
  invertibleMorphismInverseTarget := sorry
  invertibleMorphismLeftUnit := sorry
  invertibleMorphismRightUnit := sorry
  rezkEquiv := sorry
  groupoidOfAnima := fun A => ULift.up (PLift.up A.property)
  animaOfGroupoid := fun C g => ⟨C.obj, g.down.down⟩
  groupoidConstArrowFunctor := sorry
  groupoidIntervalEquiv := sorry
  animaOfGroupoidEquiv := sorry
  coreIncl := sorry
  coreUniversalPackage := sorry
  coreLiftNatIsoFromGroupoidCoherencePackage := sorry
  subcategoryPackage := sorry
  fullSubcategoryMorphismComprehensionPackage := sorry
  invertibleMorphismObjectPackage := sorry
  localizationCat := sorry
  invertingFunctorObjectPackage := sorry
  localizationFunctor := sorry
  localizationUniversalPackage := sorry
  dependentProductOverPackage := sorry
  joinCat := sorry
  joinInl := sorry
  joinInr := sorry
  joinPushoutSquare := sorry
  joinMappingOutEquiv := sorry
  joinDesc := sorry
  joinBetaLeft := sorry
  joinBetaRight := sorry
  joinDescUniq := sorry
  intervalJoinForward := sorry
  intervalJoinBackward := sorry
  intervalJoinUnit := sorry
  intervalJoinCounit := sorry
  joinDependentProductPackage := sorry
  idContextFunctor := sorry
  compContextFunctor := sorry
  idContextNatIso := sorry
  compContextNatIso := sorry
  invContextNatIso := sorry
  contextLeftUnitor := sorry
  contextRightUnitor := sorry
  contextAssocFunctor := sorry
  contextHorizCompNatIso := sorry
  contextCatEquivOfData := sorry
  contextCatEquivForward := sorry
  contextCatEquivBackward := sorry
  contextCatEquivUnit := sorry
  contextCatEquivCounit := sorry
  groupoidalContextOfAnima := sorry
  groupoidalContextOfGroupoid := sorry
  weakenContextCat := sorry
  weakenContextFunctor := sorry
  weakenContextNatIso := sorry
  weakenContextCatEquiv := sorry
  reindexContextCat := sorry
  reindexContextFunctor := sorry
  reindexContextNatIso := sorry
  reindexContextCatEquiv := sorry
  reindexContextCatId := sorry
  reindexContextCatComp := sorry
  contextTerminalCat := sorry
  contextInitialCat := sorry
  contextProdCat := sorry
  contextTerminalProjection := sorry
  contextInitialElim := sorry
  contextProdPr1 := sorry
  contextProdPr2 := sorry
  contextCoprodCat := sorry
  contextProdPair := sorry
  contextProdBeta1 := sorry
  contextProdBeta2 := sorry
  contextCoprodIn1 := sorry
  contextCoprodIn2 := sorry
  contextPullbackCat := sorry
  contextCoprodCase := sorry
  contextCoprodBeta1 := sorry
  contextCoprodBeta2 := sorry
  contextFunCat := sorry
  contextPullbackPr1 := sorry
  contextPullbackPr2 := sorry
  contextPullbackComm := sorry
  contextCoreCat := sorry
  contextSubcategory := sorry
  contextLocalization := sorry
  contextGeometricRealization := sorry
  contextJoinCat := sorry
  contextSliceCat := sorry
  sigmaCat := sorry
  sigmaPair := sorry
  sigmaDesc := sorry
  sigmaDescBeta := sorry
  sigmaDescUniq := sorry
  sigmaProjection := sorry
  sigmaLift := sorry
  sigmaTerminalUnit := sorry
  sigmaTerminalCounit := sorry
  sigmaReindexPullbackEquiv := sorry
  sigmaFunctorPullbackSquare := sorry
  sigmaSecondProjectionPullbackSquare := sorry
  sigmaPreservesPullbackEquiv := sorry
  leftAdjointSectionFunctor := sorry
  rightAdjointSectionFunctor := sorry
  directedPullbackCat := sorry
  directedPullbackPr1 := sorry
  directedPullbackPr2 := sorry
  directedPullbackArrow := sorry
  directedEval0 := sorry
  directedEval1 := sorry
  sourceFibration := sorry
  targetFibration := sorry
  sourceCartesian := sorry
  targetCocartesian := sorry
  leftFibrationEvalEquiv := sorry
  rightFibrationEvalEquiv := sorry
  baseChangeFibration := sorry
  baseChangeCartesian := sorry
  baseChangeCocartesian := sorry
  lift0Cat := sorry
  lift1Cat := sorry
  directedPullbackMapOverBase := sorry
  beckChevalleyTransformation := sorry
  idCocartesianFunctor := sorry
  compCocartesianFunctor := sorry
  adjunctionUnit := sorry
  adjunctionCounit := sorry
  leftFibrationCocartesian := sorry
  rightFibrationCartesian := sorry
  universal_left_adjoint_section := sorry
  universalLeftSectionBase := sorry
  universal_right_adjoint_section := sorry
  universalRightSectionBase := sorry
  weakenContextFibration := sorry
  pullbackShapeCat := SCTModelHelpers.pullbackShapeQCat
  pushoutShapeCat := SCTModelHelpers.pushoutShapeQCat
  locallyCocartesianOfCocartesian := sorry
  locallyCartesianOfCartesian := sorry
  coneCat := sorry
  coconeCat := sorry
  limitFunctor := sorry
  colimitFunctor := sorry
  postcompEndpointFunctorCompat := sorry
  cocartesianFunctorCategoryPackage := sorry
  universeTotalCat := sorry
  universeProjection := sorry
  universeFibration := sorry
  universeCocartesian := sorry
  universeDirectedUnivalence := sorry
  directedUnivalenceMappingEquiv := sorry
  directedUnivalenceFunctorCocartesian := sorry
  directedUnivalenceToTransformation := sorry
  smallClassifyingMap := sorry
  smallClassifyingEquiv := sorry
  smallFibrationClassifyingMap := sorry
  smallFibrationClassifyingEquiv := sorry
  cartesianFibrationExponentiable := sorry
  cocartesianFibrationExponentiable := sorry
  dependentProductTotal := sorry
  dependentProductProjection := sorry
  dependentProductFibration := sorry
  dependentProductCocartesian := sorry
  categoryUniverse := sorry
  categoryUniverseWitness := sorry
  terminalSmall := sorry
  smallProduct := sorry
  smallCoproduct := sorry
  smallPullback := sorry
  smallFunctorCategory := sorry
  smallSubcategory := sorry
  smallLocalization := sorry
  smallJoin := sorry
  smallDependentProductFibration := sorry
  smallRetract := sorry
  smallFibrationOfSmallFibers := sorry
  dependentProductSmallFibers := sorry
  smallOfSmallIntervalMap := sorry
  categoryUniverseRegular := sorry
  regularSubuniversePackage := sorry
  groupoidUniversePackage := sorry
  /- Missing: this cluster needs the universal cocartesian fibration and directed univalence;
  see Cisinski--Nguyen, `The universal coCartesian fibration`, §§7--8. -/
  directed_univalence_classifies := sorry
  isAnimaCat := fun C => PLift.{0} (SSet.KanComplex C.obj)
  anima_cat_is_anima := fun A => PLift.up A.property
  equiv_to_anima_is_anima := sorry
  sigma_anima_indexed_is_anima := sorry
  containsIdentities := sorry
  closedUnderComposition := sorry
  PreservesMorphismCollection := sorry
  LandsInObjectCollection := sorry
  InvertsMorphismCollection := sorry
  CocartesianMorphism := sorry
  CartesianMorphism := sorry
  animaIndexedFiber := sorry
  sigmaAnimaIndexedPair := sorry
  intervalZeroInitialHomContractible := sorry
  intervalOneTerminalHomContractible := sorry
  localizationInverts := sorry
  /- Missing/API target: evaluation at an object maps an equivalence edge in `Fun(A,C)` to an
  invertible edge in `C`. This is the objectwise-isomorphism theorem expected from the
  infinity-cosmos/mathlib equivalence-edge API. -/
  objectwiseNatIsoComponent := sorry
