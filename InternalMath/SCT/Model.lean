/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec
public import InternalMath.SCT.IML.Model.FiniteShapes
public import InternalMath.SCT.IML.Model.FunctorQuasicategory
public import InternalMath.SCT.IML.Model.MappingAnima
public import InternalMath.SCT.IML.Model.FibrationPullbacks
public import InternalMath.SCT.IML.Model.Localization
public import InternalMath.SCT.IML.Model.SegalComposition
public import InternalMath.SCT.IML.Model.IsoRezkModel
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# SCT model file

This file contains the generated SCT model interface and a quasicategory/Kan-complex model
skeleton. The concrete top-level carriers record the intended quasicategory semantics while the
full model is developed.

The model skeleton fills the structure directly available from mathlib: Kan complexes embed in
quasicategories, `Δ[0]` is a Kan complex, identities and composition are ordinary maps in the full
subcategory of quasicategories, and binary products of quasicategories are quasicategories. Open
`sorry`s mark genuine semantic gaps in the mathlib/SCT interface: two-cells need a bridge to
objects of functor quasicategories, pullbacks should be homotopy/∞-categorical pullbacks, and the
fibration/universe fields require the universal cocartesian fibration and directed-univalence
machinery.

Functor quasicategories use the simplicial internal hom together with mathlib's
`SSet.Quasicategory ((ihom A).obj X)` instance from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`. Natural
transformations are modeled as 2-cells in mathlib's strict bicategory of quasicategories; the bridge
from those 2-cells to objects of the functor quasicategory is the `natTransObject` field below.
The finite-shape package lives in `InternalMath.SCT.IML.Model.FiniteShapes`; the
Segal-composition scaffold lives in `InternalMath.SCT.IML.Model.SegalComposition`; the
invertible-arrow/Rezk scaffold lives in `InternalMath.SCT.IML.Model.IsoRezkModel`; the
maximal-core/mapping-anima workshop scaffold lives in `InternalMath.SCT.IML.Model.MappingAnima`;
the fibration-stable pullback scaffold lives in `InternalMath.SCT.IML.Model.FibrationPullbacks`;
the inverting-functor/localization scaffold lives in `InternalMath.SCT.IML.Model.Localization`.
-/

@[expose] public section

generate_model_interface SCT as SCTModel

open SCT CategoryTheory
open Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet

universe u

instance (C : QCat.{u}) : Quasicategory C.obj := C.property

/-- `Kan` is the category of Kan complexes, as a full subcategory of simplicial sets. -/
abbrev Kan := ObjectProperty.FullSubcategory KanComplex

instance (A : Kan.{u}) : KanComplex A.obj := A.property

namespace Kan

/-- Bundle a Kan complex as an object of `SSet.Kan`. -/
def of (S : SSet.{u}) [KanComplex S] : Kan.{u} :=
  ⟨S, inferInstance⟩

@[simp]
lemma of_obj (S : SSet.{u}) [KanComplex S] : (of S).obj = S :=
  rfl

/-- Regard a Kan complex as a quasicategory. -/
def toQCat (A : Kan.{u}) : QCat.{u} :=
  ⟨A.obj, inferInstance⟩

@[simp]
lemma toQCat_obj (A : Kan.{u}) : (toQCat A).obj = A.obj :=
  rfl

end Kan

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

namespace Subcomplex

/-- The `i`th vertex of a simplex. -/
def vertex (X : SSet.{u}) {m : SimplexCategoryᵒᵖ} (x : X.obj m)
    (i : Fin (m.unop.len + 1)) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ m.unop i).op x

@[simp]
lemma vertex_map (X : SSet.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (x : X.obj m) (i : Fin (n.unop.len + 1)) :
    vertex X (X.map f x) i = vertex X x (f.unop.toOrderHom i) := by
  dsimp [vertex]
  rw [← Functor.map_comp_apply]
  rfl

/-- The full subcomplex spanned by a predicate on vertices. -/
def fullOnVertices (X : SSet.{u}) (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj m := {x | ∀ i : Fin (m.unop.len + 1), P (vertex X x i)}
  map {m n} f x hx i := by
    rw [vertex_map]
    exact hx _

@[simp]
lemma mem_fullOnVertices_iff {X : SSet.{u}} {P : X _⦋0⦌ → Prop}
    {m : SimplexCategoryᵒᵖ} {x : X.obj m} :
    x ∈ (fullOnVertices X P).obj m ↔ ∀ i, P (vertex X x i) :=
  Iff.rfl

end Subcomplex

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
def animaCat (A : SSet.Kan.{u}) : SSet.QCat.{u} :=
  SSet.Kan.toQCat A

/-- The terminal anima is `Δ[0]`. -/
def terminalAnima : SSet.Kan.{u} :=
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

/-- A vertex of a bundled quasicategory as a map from the terminal anima. -/
def qcatPoint (C : SSet.QCat.{u}) (x : C.obj _⦋0⦌) : animaCat terminalAnima ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (SSet.yonedaEquiv.symm x)

/-- The nerve of a finite ordinal as a bundled quasicategory. -/
def finiteOrdinalQCat (n : ℕ) : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} (Fin n))

/-- The `[2]` shape, modeled as the nerve of the finite ordinal with three objects. -/
def simplex2QCat : SSet.QCat.{u} :=
  finiteOrdinalQCat 3

/-- The square shape, modeled as the nerve of the product poset `[1] × [1]`. -/
def squareQCat : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} (Fin 2 × Fin 2))

/-- A constant endomap of the walking arrow. -/
def intervalConst (i : Fin 2) : intervalQCat.{u} ⟶ intervalQCat.{u} :=
  qcatNerveMap ((Functor.const (ULift.{u} (Fin 2))).obj (ULift.up i))

/-- Pullback-indexing shape for cospans, modeled by the ordinary walking cospan nerve. -/
public def pullbackShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingCospan)

/-- Pushout-indexing shape for spans, modeled by the ordinary walking span nerve. -/
public def pushoutShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingSpan)

/-- Binary product of bundled quasicategories, using the cartesian product of simplicial sets. -/
def qcatProduct (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨C.obj ⊗ D.obj, quasicategoryTensor C.obj D.obj⟩

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

/-- If a simplicial set has no vertices, then it has no simplices in any degree. -/
@[reducible]
def isEmptyObjOfNoVertices (X : SSet.{u}) [IsEmpty (X _⦋0⦌)] (m : SimplexCategoryᵒᵖ) :
    IsEmpty (X.obj m) where
  false x := isEmptyElim (X.map (SimplexCategory.const ⦋0⦌ m.unop 0).op x)

/-- If a simplicial set has no vertices, then its type of `n`-simplices is empty. -/
@[reducible]
def isEmptySimplexOfNoVertices (X : SSet.{u}) [IsEmpty (X _⦋0⦌)] (n : ℕ) :
    IsEmpty (X _⦋n⦌) :=
  isEmptyObjOfNoVertices X _

/-- A map to the empty-nerve quasicategory forces the source to have no vertices. -/
@[reducible]
def noVerticesOfMapToInitialQCat (C : SSet.QCat.{u}) (F : C ⟶ initialQCat) :
    IsEmpty (C.obj _⦋0⦌) where
  false x := (F.hom.app _ x).obj ⟨0, by simp⟩ |>.down.elim

/-- The empty-nerve quasicategory has no vertices. -/
@[reducible]
def noVerticesInitialQCat : IsEmpty (initialQCat.{u}.obj _⦋0⦌) where
  false x := (x.obj ⟨0, by simp⟩).down.elim

/-- Maps out of a quasicategory with no vertices are unique. -/
lemma qcatHomExtOfNoVertices {C D : SSet.QCat.{u}} (hC : IsEmpty (C.obj _⦋0⦌))
    (F G : C ⟶ D) : F = G := by
  apply ObjectProperty.hom_ext
  ext m x
  exact False.elim ((isEmptyObjOfNoVertices C.obj m).false x)

/-- Assumption/local target: binary coproducts of quasicategories are quasicategories.

The expected proof is by connectedness of inner horns: a map from an inner horn to a binary
simplicial-set coproduct lands in one summand, where it can be filled. The mathlib coproduct API is
enough to package the maps below, but this closure theorem is not yet available as an imported
theorem.
-/
lemma quasicategoryCoprod (X Y : SSet.{u}) [SSet.Quasicategory X] [SSet.Quasicategory Y] :
    SSet.Quasicategory (X ⨿ Y) := by
  sorry

/-- Binary coproduct of bundled quasicategories, using the simplicial-set coproduct. -/
noncomputable def qcatCoprod (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨C.obj ⨿ D.obj, quasicategoryCoprod C.obj D.obj⟩

/-- First coproduct injection. -/
noncomputable def qcatCoprodIn1 (C D : SSet.QCat.{u}) : C ⟶ qcatCoprod C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (Limits.coprod.inl : C.obj ⟶ C.obj ⨿ D.obj)

/-- Second coproduct injection. -/
noncomputable def qcatCoprodIn2 (C D : SSet.QCat.{u}) : D ⟶ qcatCoprod C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (Limits.coprod.inr : D.obj ⟶ C.obj ⨿ D.obj)

/-- Coproduct case analysis. -/
noncomputable def qcatCoprodDesc (C D Γ : SSet.QCat.{u}) (F : C ⟶ Γ) (G : D ⟶ Γ) :
    qcatCoprod C D ⟶ Γ :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (Limits.coprod.desc F.hom G.hom)

section FunctorQuasicategoryAdapters

/-!
## Functor-quasicategory adapters

Functor objects are simplicial internal homs, bundled using the mathlib theorem that internal homs
into quasicategories are quasicategories.  The remaining `sorry`s in this section concern the bridge
from bicategorical 2-cells/equivalence edges to SCT natural-isomorphism data and are separate from
internal-hom closure.
-/

/-- The cartesian symmetry map for the pointwise product of simplicial sets. -/
def swapTensor (X Y : SSet.{u}) : X ⊗ Y ⟶ Y ⊗ X :=
  CartesianMonoidalCategory.lift
    (SemiCartesianMonoidalCategory.snd X Y)
    (SemiCartesianMonoidalCategory.fst X Y)

/-- The functor quasicategory `Fun(C,D)`, realized as the simplicial internal hom. -/
def funCat (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  SCTFunctorQuasicategory.obj C D

/-- A strict functor `C ⟶ D` as a vertex of the functor quasicategory `Fun(C,D)`. -/
def functorVertex (C D : SSet.QCat.{u}) (F : C ⟶ D) : (funCat C D).obj _⦋0⦌ :=
  SSet.unitHomEquiv (funCat C D).obj
    (MonoidalClosed.curry ((ρ_ C.obj).hom ≫ F.hom))

set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations in the SCT model are 2-cells in mathlib's strict bicategory of
quasicategories. The separate `natTransObject` model field below will connect these 2-cells with
objects of the functor quasicategory/internal hom. -/
abbrev NatTrans (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  F ⟶ G

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility evidence for a bicategorical 2-cell, used by the local quasicategory
natural-isomorphism skeleton. -/
abbrev TwoCellIsIso {C D : SSet.QCat.{u}} {F G : C ⟶ D} (α : NatTrans C D F G) : Type u :=
  ULift.{u} (PLift (IsIso α))

set_option backward.isDefEq.respectTransparency false in
/-- Package an available Lean `IsIso` instance for the local natural-isomorphism skeleton. -/
def twoCellIsIso {C D : SSet.QCat.{u}} {F G : C ⟶ D} {α : NatTrans C D F G}
    [IsIso α] : TwoCellIsIso α :=
  ULift.up (PLift.up inferInstance)

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

/-- Natural-isomorphism data in the model: an invertible bicategorical 2-cell. -/
abbrev NatIso (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  (α : NatTrans C D F G) × TwoCellIsIso α

set_option backward.isDefEq.respectTransparency false in
/-- The identity natural isomorphism. -/
def idNatIso (C D : SSet.QCat.{u}) (F : C ⟶ D) : NatIso C D F F :=
  ⟨𝟙 F, twoCellIsIso⟩

/-- Transport a natural isomorphism across equality of strict functors. -/
def natIsoOfEq {C D : SSet.QCat.{u}} {F G : C ⟶ D} (h : F = G) : NatIso C D F G := by
  subst h
  exact idNatIso C D F

set_option backward.isDefEq.respectTransparency false in
/-- Vertical composition of natural transformations as 2-cells. -/
def compNatTrans {C D : SSet.QCat.{u}} {F G H : C ⟶ D}
    (α : NatTrans C D F G) (β : NatTrans C D G H) : NatTrans C D F H :=
  α ≫ β

set_option backward.isDefEq.respectTransparency false in
/-- Invertible 2-cells are closed under vertical composition. -/
noncomputable def compTwoCellIsIso {C D : SSet.QCat.{u}} {F G H : C ⟶ D}
    {α : NatTrans C D F G} {β : NatTrans C D G H}
    (hα : TwoCellIsIso α) (hβ : TwoCellIsIso β) : TwoCellIsIso (compNatTrans α β) := by
  letI : IsIso α := hα.down.down
  letI : IsIso β := hβ.down.down
  change TwoCellIsIso (α ≫ β)
  exact twoCellIsIso

/-- Vertical composition of natural isomorphisms. -/
noncomputable def compNatIso (C D : SSet.QCat.{u}) {F G H : C ⟶ D}
    (α : NatIso C D F G) (β : NatIso C D G H) : NatIso C D F H :=
  ⟨compNatTrans α.1 β.1, compTwoCellIsIso α.2 β.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inverse of a natural isomorphism. -/
noncomputable def invNatIso (C D : SSet.QCat.{u}) {F G : C ⟶ D}
    (α : NatIso C D F G) : NatIso C D G F := by
  letI : IsIso α.1 := α.2.down.down
  exact ⟨inv α.1, twoCellIsIso⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pre-whiskering of natural isomorphisms in the strict bicategory of quasicategories. -/
noncomputable def preWhiskerNatIso (B C D : SSet.QCat.{u}) (K : B ⟶ C) {F G : C ⟶ D}
    (α : NatIso C D F G) : NatIso B D (K ≫ F) (K ≫ G) := by
  letI : IsIso α.1 := α.2.down.down
  exact ⟨Bicategory.whiskerLeft K α.1, twoCellIsIso⟩

set_option backward.isDefEq.respectTransparency false in
/-- Post-whiskering of natural isomorphisms in the strict bicategory of quasicategories. -/
noncomputable def postWhiskerNatIso (B C D : SSet.QCat.{u}) {F G : B ⟶ C} (K : C ⟶ D)
    (α : NatIso B C F G) : NatIso B D (F ≫ K) (G ≫ K) := by
  letI : IsIso α.1 := α.2.down.down
  exact ⟨Bicategory.whiskerRight α.1 K, twoCellIsIso⟩

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal composition of natural isomorphisms in the strict bicategory of quasicategories. -/
noncomputable def horizCompNatIso (B C D : SSet.QCat.{u}) {F G : B ⟶ C} {H K : C ⟶ D}
    (α : NatIso B C F G) (β : NatIso C D H K) : NatIso B D (F ≫ H) (G ≫ K) := by
  letI : IsIso α.1 := α.2.down.down
  letI : IsIso β.1 := β.2.down.down
  exact ⟨Bicategory.whiskerRight α.1 H ≫ Bicategory.whiskerLeft G β.1, twoCellIsIso⟩

/-- Equivalence of quasicategories as forward/backward functors with natural-isomorphism unit and
counit using invertible 2-cells from mathlib's strict bicategory of quasicategories.
-/
structure CatEquivData (C D : SSet.QCat.{u}) : Type u where
  forward : C ⟶ D
  backward : D ⟶ C
  unitIso : NatIso C C (forward ≫ backward) (𝟙 C)
  counitIso : NatIso D D (backward ≫ forward) (𝟙 D)

/-- A strict isomorphism of bundled quasicategories induces equivalence data. -/
def qcatCatEquivOfIso {C D : SSet.QCat.{u}} (e : C ≅ D) : CatEquivData C D where
  forward := e.hom
  backward := e.inv
  unitIso := natIsoOfEq e.hom_inv_id
  counitIso := natIsoOfEq e.inv_hom_id

/-- A strict functor as a point of the functor quasicategory. -/
def functorPoint (C D : SSet.QCat.{u}) (F : C ⟶ D) : animaCat terminalAnima ⟶ funCat C D :=
  qcatPoint (funCat C D) (functorVertex C D F)

/-- The constant-zero endomap of the interval, as a point of `Fun([1],[1])`. -/
def simplex2Id0 : animaCat terminalAnima ⟶ funCat intervalQCat intervalQCat :=
  functorPoint intervalQCat intervalQCat (intervalConst 0)

/-- The identity endomap of the interval, as a point of `Fun([1],[1])`. -/
def simplex2Can : animaCat terminalAnima ⟶ funCat intervalQCat intervalQCat :=
  functorPoint intervalQCat intervalQCat (𝟙 intervalQCat)

/-- The constant-one endomap of the interval, as a point of `Fun([1],[1])`. -/
def simplex2Id1 : animaCat terminalAnima ⟶ funCat intervalQCat intervalQCat :=
  functorPoint intervalQCat intervalQCat (intervalConst 1)

/-- A degenerate zero edge in `Fun([1],[1])`. -/
def simplex2Deg0 : animaCat terminalAnima ⟶ funCat intervalQCat intervalQCat :=
  simplex2Id0

/-- A degenerate one edge in `Fun([1],[1])`. -/
def simplex2Deg1 : animaCat terminalAnima ⟶ funCat intervalQCat intervalQCat :=
  simplex2Id1

/-- First coproduct β-comparison. -/
noncomputable def qcatCoprodBeta1 (C D Γ : SSet.QCat.{u}) (F : C ⟶ Γ) (G : D ⟶ Γ) :
    NatIso C Γ (qcatCoprodIn1 C D ≫ qcatCoprodDesc C D Γ F G) F :=
  natIsoOfEq (by
    apply ObjectProperty.hom_ext
    change (Limits.coprod.inl : C.obj ⟶ C.obj ⨿ D.obj) ≫
      Limits.coprod.desc F.hom G.hom = F.hom
    rw [Limits.coprod.inl_desc])

/-- Second coproduct β-comparison. -/
noncomputable def qcatCoprodBeta2 (C D Γ : SSet.QCat.{u}) (F : C ⟶ Γ) (G : D ⟶ Γ) :
    NatIso D Γ (qcatCoprodIn2 C D ≫ qcatCoprodDesc C D Γ F G) G :=
  natIsoOfEq (by
    apply ObjectProperty.hom_ext
    change (Limits.coprod.inr : D.obj ⟶ C.obj ⨿ D.obj) ≫
      Limits.coprod.desc F.hom G.hom = G.hom
    rw [Limits.coprod.inr_desc])

set_option backward.isDefEq.respectTransparency false in
/-- Coproduct η-comparison. -/
noncomputable def qcatCoprodEta (C D Γ : SSet.QCat.{u}) (H : qcatCoprod C D ⟶ Γ) :
    NatIso (qcatCoprod C D) Γ
      (qcatCoprodDesc C D Γ (qcatCoprodIn1 C D ≫ H) (qcatCoprodIn2 C D ≫ H)) H :=
  natIsoOfEq (by
    apply ObjectProperty.hom_ext
    change Limits.coprod.desc
      ((Limits.coprod.inl : C.obj ⟶ C.obj ⨿ D.obj) ≫ H.hom)
      ((Limits.coprod.inr : D.obj ⟶ C.obj ⨿ D.obj) ≫ H.hom) = H.hom
    apply Limits.coprod.hom_ext
    · rw [Limits.coprod.inl_desc]
    · rw [Limits.coprod.inr_desc])

/-- Strict initiality of the empty-nerve quasicategory, packaged as equivalence data. -/
def initialStrict (C : SSet.QCat.{u}) (F : C ⟶ initialQCat) : CatEquivData C initialQCat :=
  let hC := noVerticesOfMapToInitialQCat C F
  { forward := F
    backward := initialMap C
    unitIso := natIsoOfEq (qcatHomExtOfNoVertices hC (F ≫ initialMap C) (𝟙 C))
    counitIso := natIsoOfEq
      (qcatHomExtOfNoVertices noVerticesInitialQCat (initialMap C ≫ F) (𝟙 initialQCat)) }

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

end FunctorQuasicategoryAdapters

end SCTModelHelpers

namespace SCTModelHelpers

/-- Model-side interpretation of `NatIso` using the admitted `ObjectwiseNatIsoData` `syntax_def`.
The natural-transformation component is kept from the quasicategory skeleton; the objectwise package
is admitted SCT debt. -/
abbrev ModelObjectwiseNatIsoData (C D : SSet.QCat.{u}) (F G : C ⟶ D)
    (α : NatTrans C D F G) : Type u :=
  SCTModel_ObjectwiseNatIsoData_syntaxDef SSet.QCat (fun C D => C ⟶ D)
    (fun {C D} F G => NatTrans C D F G) F G α

/-- The generated model type for natural isomorphisms. -/
abbrev ModelNatIso (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  Σ natIsoTrans : NatTrans C D F G, ModelObjectwiseNatIsoData C D F G natIsoTrans

/-- Convert the existing quasicategory natural-isomorphism skeleton to the generated model type. -/
noncomputable def toModelNatIso {C D : SSet.QCat.{u}} {F G : C ⟶ D}
    (α : NatIso C D F G) : ModelNatIso C D F G :=
  ⟨α.1, sorry⟩

/-- Convert generated model natural-isomorphism data back to the local skeleton type. -/
noncomputable def ofModelNatIso {C D : SSet.QCat.{u}} {F G : C ⟶ D}
    (α : ModelNatIso C D F G) : NatIso C D F G :=
  ⟨α.1, sorry⟩

end SCTModelHelpers

set_option backward.isDefEq.respectTransparency false in
noncomputable def sctModel.{u} : SCTModel.{u} where
  Anima := SSet.Kan.{u}
  SCat := SSet.QCat.{u}
  Functor C D := C ⟶ D
  NatTrans := fun {C D} F G => SCTModelHelpers.NatTrans C D F G
  CatEquiv := SCTModelHelpers.CatEquivData
  AnimaIndexedCat := sorry
  GroupoidWitness C := ULift.{u} (PLift (SSet.KanComplex C.obj))
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
  leftAdjointSectionFunctor := sorry
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
  idFunctor C := 𝟙 C
  compFunctor F G := F ≫ G
  idNatIso {C} {D} F := SCTModelHelpers.toModelNatIso (SCTModelHelpers.idNatIso C D F)
  compNatIso {C} {D} {_F} {_G} {_H} α β := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.compNatIso C D (SCTModelHelpers.ofModelNatIso α)
      (SCTModelHelpers.ofModelNatIso β))
  invNatIso {C} {D} {_F} {_G} α := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.invNatIso C D (SCTModelHelpers.ofModelNatIso α))
  leftUnitor _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq (by simp))
  rightUnitor _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq (by simp))
  assocFunctor _ _ _ := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.natIsoOfEq (by simp [Category.assoc]))
  preWhiskerNatIso {B} {C} {D} K {_F} {_G} α := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.preWhiskerNatIso B C D K (SCTModelHelpers.ofModelNatIso α))
  postWhiskerNatIso {B} {C} {D} {_F} {_G} K α := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.postWhiskerNatIso B C D K (SCTModelHelpers.ofModelNatIso α))
  horizCompNatIso {B} {C} {D} {_F} {_G} {_H} {_K} α β := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.horizCompNatIso B C D (SCTModelHelpers.ofModelNatIso α)
      (SCTModelHelpers.ofModelNatIso β))
  catEquivOfData F G η ε :=
    ⟨F, G, SCTModelHelpers.ofModelNatIso η, SCTModelHelpers.ofModelNatIso ε⟩
  catEquivForward e := e.forward
  catEquivBackward e := e.backward
  catEquivUnit e := SCTModelHelpers.toModelNatIso e.unitIso
  catEquivCounit e := SCTModelHelpers.toModelNatIso e.counitIso
  terminalAnima := SCTModelHelpers.terminalAnima
  terminalProjection := SCTModelHelpers.terminalProjection
  terminalUnique _ _ _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq (by
    apply ObjectProperty.hom_ext
    exact SSet.stdSimplex.ext₀))
  initialCat := SCTModelHelpers.initialQCat
  initialElim := SCTModelHelpers.initialMap
  initialUnique _ _ _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq (by
    apply ObjectProperty.hom_ext
    ext n x
    exact False.elim (x.obj ⟨0, by simp⟩).down.elim))
  initialStrict := SCTModelHelpers.initialStrict
  prodCat := SCTModelHelpers.qcatProduct
  prodPr1 := SCTModelHelpers.qcatProdPr1
  prodPr2 := SCTModelHelpers.qcatProdPr2
  prodPair := SCTModelHelpers.qcatProdPair
  prodBeta1 _ _ _ _ _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq rfl)
  prodBeta2 _ _ _ _ _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq rfl)
  prodEta _ _ _ _ := SCTModelHelpers.toModelNatIso (SCTModelHelpers.natIsoOfEq rfl)
  prodUniq := sorry
  coprodCat := SCTModelHelpers.qcatCoprod
  coprodIn1 := SCTModelHelpers.qcatCoprodIn1
  coprodIn2 := SCTModelHelpers.qcatCoprodIn2
  coprodCase := SCTModelHelpers.qcatCoprodDesc
  coprodBeta1 C D Γ F G :=
    SCTModelHelpers.toModelNatIso (SCTModelHelpers.qcatCoprodBeta1 C D Γ F G)
  coprodBeta2 C D Γ F G :=
    SCTModelHelpers.toModelNatIso (SCTModelHelpers.qcatCoprodBeta2 C D Γ F G)
  coprodEta C D Γ H := SCTModelHelpers.toModelNatIso (SCTModelHelpers.qcatCoprodEta C D Γ H)
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
  selfPullbackDiagonal := sorry
  coprodBaseChangeForward := sorry
  coprodBaseChangeBackward := sorry
  coprodBaseChangeUnit := sorry
  coprodBaseChangeCounit := sorry
  coprodDisjointForward := sorry
  coprodDisjointBackward := sorry
  coprodDisjointUnit := sorry
  coprodDisjointCounit := sorry
  funCat := SCTModelHelpers.funCat
  pullbackConeEquiv := sorry
  evalFunctor := SCTModelHelpers.evalFunctor
  curryFunctor := SCTModelHelpers.curryFunctor
  uncurryFunctor := SCTModelHelpers.uncurryFunctor
  curryBeta Γ C D F := SCTModelHelpers.toModelNatIso (SCTModelHelpers.curryBeta Γ C D F)
  curryEta Γ C D F := SCTModelHelpers.toModelNatIso (SCTModelHelpers.curryEta Γ C D F)
  curryNatIso Γ C D _ _ α := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.curryNatIso Γ C D (SCTModelHelpers.ofModelNatIso α))
  uncurryNatIso Γ C D _ _ α := SCTModelHelpers.toModelNatIso
    (SCTModelHelpers.uncurryNatIso Γ C D (SCTModelHelpers.ofModelNatIso α))
  curryUncurryForward := SCTModelHelpers.curryUncurryForward
  curryUncurryBackward := SCTModelHelpers.curryUncurryBackward
  curryUncurryUnit Γ C D :=
    SCTModelHelpers.toModelNatIso (SCTModelHelpers.curryUncurryUnit Γ C D)
  curryUncurryCounit Γ C D :=
    SCTModelHelpers.toModelNatIso (SCTModelHelpers.curryUncurryCounit Γ C D)
  intervalCat := SCTModelHelpers.intervalQCat
  intervalZero := SCTModelHelpers.intervalVertex 0
  intervalOne := SCTModelHelpers.intervalVertex 1
  /- Missing: the remaining model-facing low-dimensional face data should be transported from the
  usual simplex maps. -/
  simplex2Face02 := SCTSegalCompositionSkeleton.ModelBridge.simplex2Face02
  functorObjectSourceCompat := sorry
  functorObjectTargetCompat := sorry
  natTransObject := sorry
  pullbackUniqCone := sorry
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
  rezkEquiv := sorry
  groupoidOfAnima A := ULift.up (PLift.up A.property)
  animaOfGroupoid C g := ⟨C.obj, g.down.down⟩
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
  isAnimaCat C := PLift.{0} (SSet.KanComplex C.obj)
  anima_cat_is_anima A := PLift.up A.property
  equiv_to_anima_is_anima := sorry
  sigma_anima_indexed_is_anima := sorry
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
