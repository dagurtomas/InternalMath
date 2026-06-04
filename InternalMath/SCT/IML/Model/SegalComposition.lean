/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.IML.Model.FiniteShapes

/-!
# Segal composition and arrow calculus skeleton

This file gives a model-side scaffold for the SCT project that interprets composition of
interval-shaped arrows by filling the inner horn `Λ[2,1] -> C` in a quasicategory. The companion
blueprint is `Docs/SCT/IML/Model/SegalCompositionBlueprint.md`.

The finite shape maps are provided by `InternalMath.SCT.IML.Model.FiniteShapes`: `[0]`, `[1]`,
`[2]`, the three faces of `[2]`, the degeneracy `[1] -> [0]`, and the square `[1] × [1]`.

The declarations below are honest interfaces. The chosen filler is noncomputable and currently a
project marker. Unit and associativity comparisons are not strict equalities of fillers; they should
be packaged as the model's bicategorical `NatIso`/comparison data once the functor-quasicategory
bridge is available.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SCTSegalCompositionSkeleton

universe u

namespace IntervalArrow

/-- An interval-shaped arrow in a quasicategory. -/
abbrev Arrow (C : SSet.QCat.{u}) : Type u :=
  SCTFiniteShapes.interval ⟶ C

/-- The source endpoint of an interval-shaped arrow. -/
def source {C : SSet.QCat.{u}} (f : Arrow C) : SCTFiniteShapes.point ⟶ C :=
  SCTFiniteShapes.vertex 1 0 ≫ f

/-- The target endpoint of an interval-shaped arrow. -/
def target {C : SSet.QCat.{u}} (f : Arrow C) : SCTFiniteShapes.point ⟶ C :=
  SCTFiniteShapes.vertex 1 1 ≫ f

/-- The identity interval arrow at an object of `C`, using the degeneracy `[1] -> [0]`. -/
def idAt {C : SSet.QCat.{u}} (x : SCTFiniteShapes.point ⟶ C) : Arrow C :=
  SCTFiniteShapes.intervalDegeneracy ≫ x

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma source_idAt {C : SSet.QCat.{u}} (x : SCTFiniteShapes.point ⟶ C) :
    source (idAt x) = x := by
  unfold source idAt
  rw [← Category.assoc, SCTFiniteShapes.intervalDegeneracy_vertex_zero, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma target_idAt {C : SSet.QCat.{u}} (x : SCTFiniteShapes.point ⟶ C) :
    target (idAt x) = x := by
  unfold target idAt
  rw [← Category.assoc, SCTFiniteShapes.intervalDegeneracy_vertex_one, Category.id_comp]

end IntervalArrow

open IntervalArrow

/-- A strictly composable pair of interval-shaped arrows.

This strict endpoint equality is only a shape-level way to specify a horn. The later SCT comparison
fields should use bicategorical natural-isomorphism data where the book asks for comparisons.
-/
structure ComposablePair (C : SSet.QCat.{u}) : Type u where
  first : Arrow C
  second : Arrow C
  matching : target first = source second

namespace ComposablePair

/-- The left-unit composable pair `(id_source f, f)`. -/
def leftUnit {C : SSet.QCat.{u}} (f : Arrow C) : ComposablePair C where
  first := idAt (source f)
  second := f
  matching := by simp

/-- The right-unit composable pair `(f, id_target f)`. -/
def rightUnit {C : SSet.QCat.{u}} (f : Arrow C) : ComposablePair C where
  first := f
  second := idAt (target f)
  matching := by simp

end ComposablePair

/-- A `2`-simplex filling the composable-pair horn. -/
structure TriangleFiller {C : SSet.QCat.{u}} (p : ComposablePair C) : Type u where
  simplex : SCTFiniteShapes.triangle ⟶ C
  face01 : SCTFiniteShapes.simplex2Face01 ≫ simplex = p.first
  face12 : SCTFiniteShapes.simplex2Face12 ≫ simplex = p.second

namespace TriangleFiller

/-- The composite edge of a chosen triangle filler, namely the `0 -> 2` face. -/
def composite {C : SSet.QCat.{u}} {p : ComposablePair C} (t : TriangleFiller p) : Arrow C :=
  SCTFiniteShapes.simplex2Face02 ≫ t.simplex

set_option backward.isDefEq.respectTransparency false in
/-- The composite has the source of the first arrow in the chosen triangle. -/
lemma composite_source {C : SSet.QCat.{u}} {p : ComposablePair C} (t : TriangleFiller p) :
    source (composite t) = source p.first := by
  unfold source composite
  rw [← Category.assoc, SCTFiniteShapes.simplex2Face02_vertex_zero]
  rw [← t.face01]
  rw [← Category.assoc, SCTFiniteShapes.simplex2Face01_vertex_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The composite has the target of the second arrow in the chosen triangle. -/
lemma composite_target {C : SSet.QCat.{u}} {p : ComposablePair C} (t : TriangleFiller p) :
    target (composite t) = target p.second := by
  unfold target composite
  rw [← Category.assoc, SCTFiniteShapes.simplex2Face02_vertex_one]
  rw [← t.face12]
  rw [← Category.assoc, SCTFiniteShapes.simplex2Face12_vertex_one]

end TriangleFiller

/-- Chosen Segal filler for a composable pair.

The intended proof constructs the inner horn `Λ[2,1] -> C` from `p.first`, `p.second`, and
`p.matching`, then applies the quasicategory horn-filling theorem. The filler is not unique on the
nose.
-/
noncomputable def chosenFiller {C : SSet.QCat.{u}} (p : ComposablePair C) : TriangleFiller p := by
  sorry

/-- Chosen composite of a composable pair. -/
noncomputable def composite {C : SSet.QCat.{u}} (p : ComposablePair C) : Arrow C :=
  TriangleFiller.composite (chosenFiller p)

/-- Comparison data between interval-shaped arrows.

In the SCT model this should be supplied by bicategorical `NatIso` data between the corresponding
functors `[1] -> C`, not by strict equality of chosen fillers.
-/
def ArrowComparison {C : SSet.QCat.{u}} (_f _g : Arrow C) : Type (u + 1) := by
  sorry

/-- Left-unit comparison target for Segal composition. -/
def LeftUnitComparison {C : SSet.QCat.{u}} (f : Arrow C) : Type (u + 1) :=
  ArrowComparison (composite (ComposablePair.leftUnit f)) f

/-- Right-unit comparison target for Segal composition. -/
def RightUnitComparison {C : SSet.QCat.{u}} (f : Arrow C) : Type (u + 1) :=
  ArrowComparison (composite (ComposablePair.rightUnit f)) f

/-- A strictly composable triple of interval-shaped arrows. -/
structure ComposableTriple (C : SSet.QCat.{u}) : Type u where
  first : Arrow C
  second : Arrow C
  third : Arrow C
  match12 : target first = source second
  match23 : target second = source third

namespace ComposableTriple

/-- The left-associated pair `(first ; second) ; third`, as future comparison input. -/
def leftAssociatedPair {C : SSet.QCat.{u}} (t : ComposableTriple C) : Type u :=
  { p12 : ComposablePair C //
    p12.first = t.first ∧ p12.second = t.second ∧ target (composite p12) = source t.third }

/-- The right-associated pair `first ; (second ; third)`, as future comparison input. -/
def rightAssociatedPair {C : SSet.QCat.{u}} (t : ComposableTriple C) : Type u :=
  { p23 : ComposablePair C //
    p23.first = t.second ∧ p23.second = t.third ∧ target t.first = source (composite p23) }

end ComposableTriple

/-- Associativity comparison target for the chosen Segal composition.

The actual theorem should compare the two composites using a `3`-simplex/pasting argument and
package the result as bicategorical comparison data.
-/
def AssociativityComparison {C : SSet.QCat.{u}} (t : ComposableTriple C) : Type (u + 1) := by
  sorry

namespace ModelBridge

/-!
## Bridge to the generated SCT model fields

The generated SCT model presents `simplex2Cat` as `Fun([1],[1])`, while the finite-shape package
presents `[2]` as a standard simplex. The bridge between these descriptions is the usual
identification of monotone maps `[m] -> [2]` with monotone families of endomaps of `[1]`, i.e. a map
`[m] × [1] -> [1]`. The declarations in this namespace name that bridge so that `Model.lean` can
refer to project files rather than carrying local `sorry`s.
-/

/-- The walking-arrow quasicategory in the generated SCT model's nerve presentation. -/
def intervalQCat : SSet.QCat.{u} :=
  SCTFiniteShapes.nerveQCat (ULift.{u} (Fin 2))

/-- API target: the simplicial internal hom of quasicategories is a quasicategory. -/
lemma quasicategoryInternalHom (C D : SSet.QCat.{u}) :
    SSet.Quasicategory ((ihom C.obj).obj D.obj) := by
  sorry

/-- The functor quasicategory, realized as a simplicial internal hom. -/
def funCat (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨(ihom C.obj).obj D.obj, quasicategoryInternalHom C D⟩

set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations are bicategorical 2-cells. -/
abbrev NatTrans (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  F ⟶ G

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility evidence for bicategorical 2-cells, universe-lifted for the model interface. -/
abbrev TwoCellIsIso {C D : SSet.QCat.{u}} {F G : C ⟶ D}
    (α : NatTrans C D F G) : Type u :=
  ULift.{u} (PLift (IsIso α))

/-- Natural-isomorphism data used by the generated SCT model. -/
abbrev NatIso (C D : SSet.QCat.{u}) (F G : C ⟶ D) : Type u :=
  (α : NatTrans C D F G) × TwoCellIsIso α

/-- The face of `Fun([1],[1])` from the constant-zero endomap to the identity endomap.

This is the `0 -> 1` edge of the bridge `[2] ≃ Fun([1],[1])`. Its construction is the monotone
family `min : [1] × [1] -> [1]`, curried into the internal hom.
-/
noncomputable def simplex2Face01 : intervalQCat.{u} ⟶ funCat intervalQCat intervalQCat := by
  sorry

/-- The face of `Fun([1],[1])` from the identity endomap to the constant-one endomap.

This is the `1 -> 2` edge of the bridge `[2] ≃ Fun([1],[1])`. Its construction is the monotone
family `max : [1] × [1] -> [1]`, curried into the internal hom.
-/
noncomputable def simplex2Face12 : intervalQCat.{u} ⟶ funCat intervalQCat intervalQCat := by
  sorry

/-- The face of `Fun([1],[1])` from the constant-zero endomap to the constant-one endomap.

This is the `0 -> 2` edge of the bridge `[2] ≃ Fun([1],[1])`. Its construction is the first
projection `[1] × [1] -> [1]`, curried into the internal hom.
-/
noncomputable def simplex2Face02 : intervalQCat.{u} ⟶ funCat intervalQCat intervalQCat := by
  sorry

/-- Endpoint compatibility for the `0 -> 1` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face01Zero {T : SSet.QCat.{u}}
    (simplex2Id0 : T ⟶ funCat intervalQCat intervalQCat)
    (intervalZero : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalZero ≫ simplex2Face01)
      simplex2Id0 := by
  sorry

/-- Endpoint compatibility for the `0 -> 1` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face01One {T : SSet.QCat.{u}}
    (simplex2Can : T ⟶ funCat intervalQCat intervalQCat)
    (intervalOne : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalOne ≫ simplex2Face01)
      simplex2Can := by
  sorry

/-- Endpoint compatibility for the `1 -> 2` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face12Zero {T : SSet.QCat.{u}}
    (simplex2Can : T ⟶ funCat intervalQCat intervalQCat)
    (intervalZero : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalZero ≫ simplex2Face12)
      simplex2Can := by
  sorry

/-- Endpoint compatibility for the `1 -> 2` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face12One {T : SSet.QCat.{u}}
    (simplex2Id1 : T ⟶ funCat intervalQCat intervalQCat)
    (intervalOne : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalOne ≫ simplex2Face12)
      simplex2Id1 := by
  sorry

/-- Endpoint compatibility for the `0 -> 2` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face02Zero {T : SSet.QCat.{u}}
    (simplex2Id0 : T ⟶ funCat intervalQCat intervalQCat)
    (intervalZero : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalZero ≫ simplex2Face02)
      simplex2Id0 := by
  sorry

/-- Endpoint compatibility for the `0 -> 2` face of `Fun([1],[1])`. -/
noncomputable def simplex2Face02One {T : SSet.QCat.{u}}
    (simplex2Id1 : T ⟶ funCat intervalQCat intervalQCat)
    (intervalOne : T ⟶ intervalQCat) :
    NatIso T (funCat intervalQCat intervalQCat) (intervalOne ≫ simplex2Face02)
      simplex2Id1 := by
  sorry

end ModelBridge

end SCTSegalCompositionSkeleton
