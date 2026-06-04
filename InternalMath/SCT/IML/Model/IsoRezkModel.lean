/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.IML.Model.FiniteShapes
public import InternalMath.SCT.IML.Model.MappingAnima

/-!
# Invertible arrows, `Iso(C)`, and Rezk completeness skeleton

This file gives a model-side scaffold for the SCT project that builds the category of invertible
arrows `Iso(C)` and relates it to Rezk completeness. It is a companion to
`Docs/SCT/IML/Model/IsoRezkModelBlueprint.md`.

The scaffold separates the pieces supplied by mathlib PR #35287 from the SCT-specific work.

PR #35287 is expected to cover the following low-level simplicial-set API:

* `SSet.Edge.InvStruct hom`, with inverse edge, `hom ≫ inv = id`, and `inv ≫ hom = id`
  triangle data;
* identity inverse structures, inverse-of-inverse, preservation under simplicial maps, and
  transport along equality of underlying one-simplices;
* `SSet.coherentIso`, the nerve of the walking isomorphism;
* the source, target, forward, and backward edges of `coherentIso`;
* `coherentIso.invStructHom`, and a theorem giving inverse structure to any edge that is the image
  of the forward coherent-isomorphism edge.

The PR does not build the SCT interval-functor adapters, does not connect the inverse triangles to
the chosen Segal composition operation, does not construct the object collection of invertible
arrows in `Fun([1], C)`, does not build the full subcategory `Iso(C)`, and does not prove the Rezk
comparison equivalence. Those items remain the project tracked here.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SCTIsoRezkModelSkeleton

universe u

namespace IncomingPR35287

/-- Local shape of the inverse-edge data expected from mathlib PR #35287.

Once the PR is available, this should be replaced by `SSet.Edge.InvStruct`. The PR supplies this
edge-level data and basic operations on it; the rest of this file records the adapters still needed
for SCT.
-/
structure EdgeInvStruct {X : SSet.{u}} {x y : X _⦋0⦌} (hom : SSet.Edge x y) where
  /-- The inverse edge. -/
  inv : SSet.Edge y x
  /-- A `2`-simplex witnessing that the forward edge followed by the inverse is the identity. -/
  homInvId : SSet.Edge.CompStruct hom inv (SSet.Edge.id x)
  /-- A `2`-simplex witnessing that the inverse followed by the forward edge is the identity. -/
  invHomId : SSet.Edge.CompStruct inv hom (SSet.Edge.id y)

/-- The identity edge has inverse-edge data. This is one of the operations covered by PR #35287. -/
def id {X : SSet.{u}} (x : X _⦋0⦌) : EdgeInvStruct (SSet.Edge.id x) where
  inv := SSet.Edge.id x
  homInvId := SSet.Edge.CompStruct.idComp (SSet.Edge.id x)
  invHomId := SSet.Edge.CompStruct.idComp (SSet.Edge.id x)

/-- The inverse of an invertible edge is invertible. This is covered by PR #35287. -/
def symm {X : SSet.{u}} {x y : X _⦋0⦌} {e : SSet.Edge x y}
    (h : EdgeInvStruct e) : EdgeInvStruct h.inv where
  inv := e
  homInvId := h.invHomId
  invHomId := h.homInvId

end IncomingPR35287

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

/-- The one-simplex classified by an interval-shaped arrow. -/
def simplex {C : SSet.QCat.{u}} (f : Arrow C) : C.obj _⦋1⦌ :=
  SSet.yonedaEquiv f.hom

/-- The edge classified by an interval-shaped arrow. -/
def edge {C : SSet.QCat.{u}} (f : Arrow C) :
    SSet.Edge (C.obj.δ 1 (simplex f)) (C.obj.δ 0 (simplex f)) :=
  SSet.Edge.mk' (simplex f)

/-- Turn a one-simplex into an interval-shaped arrow. -/
def ofSimplex (C : SSet.QCat.{u}) (s : C.obj _⦋1⦌) : Arrow C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (SSet.yonedaEquiv.symm s)

/-- Inverse interval arrow obtained from inverse-edge data.

PR #35287 supplies the inverse edge data used here. The remaining SCT work is to prove endpoint
compatibility and unit comparisons for the synthetic interval-functor operations.
-/
def inverseFromInvStruct {C : SSet.QCat.{u}} (f : Arrow C)
    (h : IncomingPR35287.EdgeInvStruct (edge f)) : Arrow C :=
  ofSimplex C h.inv.edge

/-- Endpoint comparisons required by the SCT model for the inverse interval arrow.

The PR gives the endpoints of the inverse edge at the raw `SSet.Edge` level. It does not prove these
comparisons between interval-shaped functors and the model's source/target maps.
-/
def InverseEndpointComparisons {C : SSet.QCat.{u}} (f : Arrow C)
    (h : IncomingPR35287.EdgeInvStruct (edge f)) : Prop :=
  source (inverseFromInvStruct f h) = target f ∧
    target (inverseFromInvStruct f h) = source f

/-- Adapter target: inverse-edge data gives the endpoint comparisons required by SCT. -/
lemma inverseEndpointComparisons {C : SSet.QCat.{u}} (f : Arrow C)
    (h : IncomingPR35287.EdgeInvStruct (edge f)) : InverseEndpointComparisons f h := by
  sorry

end IntervalArrow

namespace SegalInterface

open IntervalArrow

/-- Unit comparison data connecting inverse-edge triangles with the chosen Segal composition.

PR #35287 supplies the two raw `2`-simplices in `Edge.InvStruct`. It does not identify those
simplices with the noncomputable composites chosen by the SCT Segal-composition package. This type
is a placeholder for those comparison theorems.
-/
def InverseUnitComparisons {C : SSet.QCat.{u}} (f : Arrow C)
    (h : IncomingPR35287.EdgeInvStruct (edge f)) : Prop := by
  sorry

end SegalInterface

namespace InvertibleArrows

open IntervalArrow

/-- Invertible interval-shaped arrow data, using the PR #35287 edge-level inverse structure.

This is the intended model-side interpretation of SCT's `InvertibleMorphismData` after the incoming
PR is available.
-/
structure Data {C : SSet.QCat.{u}} (f : Arrow C) : Type u where
  invStruct : IncomingPR35287.EdgeInvStruct (edge f)
  endpoints : InverseEndpointComparisons f invStruct
  units : SegalInterface.InverseUnitComparisons f invStruct

/-- The inverse arrow determined by invertible interval-shaped arrow data. -/
def inverse {C : SSet.QCat.{u}} {f : Arrow C} (h : Data f) : Arrow C :=
  inverseFromInvStruct f h.invStruct

end InvertibleArrows

namespace IsoCategory

open IntervalArrow

/-- The functor quasicategory `Fun([1], C)` used as the arrow category.

This should come from the same internal-hom/functor-quasicategory API used by the SCT model. It is
not part of PR #35287.
-/
noncomputable def arrowFunctorQCat (C : SSet.QCat.{u}) : SSet.QCat.{u} := by
  sorry

/-- Object collection in `Fun([1], C)` spanned by invertible interval arrows.

PR #35287 supplies the raw inverse-edge predicate/data. This object collection still requires the
functor-quasicategory bridge, object collections/full subcategories, and the adapter between
vertices of `Fun([1], C)` and interval-shaped arrows.
-/
def InvertibleArrowObjectCollection (C : SSet.QCat.{u}) : Type (u + 1) := by
  sorry

/-- Full-subcategory witness for the invertible-arrow object collection.

This should eventually be the full subquasicategory of `Fun([1], C)` on invertible arrows, with the
inclusion into the arrow functor quasicategory.
-/
def FullSubcategoryWitness (C IsoC : SSet.QCat.{u})
    (incl : IsoC ⟶ arrowFunctorQCat C) : Type (u + 1) := by
  sorry

/-- Candidate for `Iso(C)`: a full subcategory of the arrow functor quasicategory. -/
structure Candidate (C : SSet.QCat.{u}) : Type (u + 1) where
  obj : SSet.QCat.{u}
  incl : obj ⟶ arrowFunctorQCat C
  objects : InvertibleArrowObjectCollection C
  fullSubcategory : FullSubcategoryWitness C obj incl

/-- Construction target for `Iso(C)`. This is not supplied by PR #35287. -/
noncomputable def candidate (C : SSet.QCat.{u}) : Candidate C := by
  sorry

end IsoCategory

namespace Rezk

/-- Rezk comparison/equivalence data between a quasicategory and its category of isomorphisms.

This is a high-level quasicategorical theorem. PR #35287 does not prove it; the proof depends on
the full `Iso(C)` construction and the model's `CatEquiv`/bicategorical natural-isomorphism API.
-/
def EquivalenceData (C IsoC : SSet.QCat.{u}) : Type (u + 1) := by
  sorry

/-- Rezk completeness target for the candidate `Iso(C)`. -/
def UniversalProperty (C : SSet.QCat.{u}) (iso : IsoCategory.Candidate C) : Type (u + 1) :=
  EquivalenceData C iso.obj

/-- Final project target: `C` is equivalent to its quasicategory of invertible arrows. -/
noncomputable def comparison (C : SSet.QCat.{u}) :
    UniversalProperty C (IsoCategory.candidate C) := by
  sorry

end Rezk

end SCTIsoRezkModelSkeleton
