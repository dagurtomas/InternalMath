/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.MappingAnima
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory

/-!
# Inverting-functor categories and localization skeleton

This file gives a model-side scaffold for the workshop project on functors that invert a chosen
morphism collection and on quasicategorical localization.  It is not a construction of localizations
in mathlib.  The declarations below mark the semantic interfaces needed to interpret SCT Axiom I in
the quasicategory model.

The intended semantics is:

* a morphism collection `W` in a quasicategory `C` is a subobject of the mapping anima of arrows in
  `C`;
* a functor `F : C ⟶ D` inverts `W` when every arrow selected by `W` is sent to an equivalence edge
  in `D`;
* `Fun_W(C,D)` is the full sub-quasicategory of `Fun(C,D)` on such functors;
* a localization `C[W⁻¹]` is a quasicategory with `loc : C ⟶ C[W⁻¹]` inverting `W` and universal
  among functors that invert `W`.

The universal property must be quasicategorical, preferably stated through mapping anima.  Ordinary
localization of the homotopy category is not the intended interpretation.  In the current SCT model,
natural transformations are bicategorical 2-cells; this scaffold still needs the bridge from those
2-cells to the functor quasicategory when forming inverting-functor subcategories.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SCTLocalizationSkeleton

universe u

namespace FunctorQuasicategory

/-- The quasicategory of functors between two quasicategories.

To make this construction correct, use the simplicial internal hom `D.obj ^ C.obj` and prove the
standard theorem that it is a quasicategory whenever `C` and `D` are quasicategories.  This should
later be replaced by the same upstream functor-quasicategory/internal-hom API used by the SCT model.
-/
noncomputable def obj (C D : SSet.QCat.{u}) : SSet.QCat.{u} := by
  sorry

end FunctorQuasicategory

/-- A chosen collection of morphisms in a quasicategory.

To make this definition correct, represent `W` as a subobject of the arrow mapping anima
`Map(Δ[1], C)`, equivalently a Kan subcomplex/sub-anima of the maximal core of the arrow functor
quasicategory.  Its points should be interval-shaped arrows of `C`, and its inclusion should be an
embedding of anima.
-/
def MorphismCollection (C : SSet.QCat.{u}) : Type (u + 1) := by
  sorry

/-- Evidence that a functor sends the chosen morphism collection to equivalences.

To make this predicate correct, evaluate `F : C ⟶ D` on the arrow objects classified by `W` and
require the resulting arrows of `D` to land in the invertible-arrow object, or equivalently in the
maximal core of `Fun(Δ[1], D)`.  The construction should use functoriality of arrow categories and
preservation of equivalence edges by simplicial maps.
-/
def Inverts {C D : SSet.QCat.{u}} (W : MorphismCollection C) (F : C ⟶ D) : Prop := by
  sorry

namespace InvertingFunctorCategory

variable {C : SSet.QCat.{u}}

/-- The full sub-quasicategory of `Fun(C,D)` spanned by functors that invert `W`.

To make this construction correct, first build the object collection of vertices of `Fun(C,D)` that
satisfy `Inverts W`.  Then apply the full-subcategory construction for quasicategories.  The result
should come with a full-subcategory inclusion into `Fun(C,D)` and an objectwise equivalence between
membership and `Inverts W`.
-/
noncomputable def obj (W : MorphismCollection C) (D : SSet.QCat.{u}) : SSet.QCat.{u} := by
  sorry

/-- Inclusion of the inverting-functor category into the ordinary functor quasicategory.

To make this construction correct, use the inclusion supplied by the full-subcategory construction
for the object collection of functors satisfying `Inverts W`.  Its vertices are the same functors
`C ⟶ D`, now equipped with evidence that they invert `W`.
-/
noncomputable def incl (W : MorphismCollection C) (D : SSet.QCat.{u}) :
    obj W D ⟶ FunctorQuasicategory.obj C D := by
  sorry

end InvertingFunctorCategory

namespace Localization

variable {C L D : SSet.QCat.{u}}

/-- Precomposition with a localization candidate, landing in inverting functors.

To make this construction correct, send a functor `K : L ⟶ D` to `loc ≫ K : C ⟶ D`.  The proof
that this composite inverts `W` comes from `hloc` together with preservation of equivalence edges by
`K`.  This is the canonical comparison functor used in the localization universal property.
-/
noncomputable def precomp (W : MorphismCollection C) (loc : C ⟶ L)
    (hloc : Inverts W loc) (D : SSet.QCat.{u}) :
    FunctorQuasicategory.obj L D ⟶ InvertingFunctorCategory.obj W D := by
  sorry

/-- The quasicategorical universal property of localization.

To make this definition correct, replace the placeholder by a structure asserting that, for every
quasicategory `D`, the comparison
`Fun(L,D) → Fun_W(C,D)` induced by precomposition with `loc` is an equivalence of quasicategories,
or equivalently that the induced map on mapping anima is an equivalence.  The structure should also
provide the descent functor, β comparison, and uniqueness comparison used by the generated SCT model
interface.
-/
def UniversalProperty (W : MorphismCollection C) (loc : C ⟶ L) (hloc : Inverts W loc) :
    Type (u + 1) := by
  sorry

/-- A localization candidate: object, localization functor, inversion evidence, and universal
property.

This structure is correct only when `universal` contains the quasicategorical universal property
above.  The first three fields alone merely say that `loc` sends the selected arrows to
equivalences; they do not identify `obj` with the localization.
-/
structure Candidate (C : SSet.QCat.{u}) (W : MorphismCollection C) : Type (u + 1) where
  obj : SSet.QCat.{u}
  loc : C ⟶ obj
  inverts : Inverts W loc
  universal : UniversalProperty W loc inverts

/-- Existence of the localization of a quasicategory at a morphism collection.

To make this construction correct, import or formalize the quasicategorical/Dwyer--Kan
localization theorem.  The produced object must satisfy the universal property above, not just the
ordinary localization of the homotopy category.
-/
noncomputable def candidate (C : SSet.QCat.{u}) (W : MorphismCollection C) :
    Candidate C W := by
  sorry

/-- The localized quasicategory `C[W⁻¹]`. -/
noncomputable def cat (C : SSet.QCat.{u}) (W : MorphismCollection C) : SSet.QCat.{u} :=
  (candidate C W).obj

/-- The localization functor `C ⟶ C[W⁻¹]`. -/
noncomputable def functor (C : SSet.QCat.{u}) (W : MorphismCollection C) : C ⟶ cat C W :=
  (candidate C W).loc

/-- The localization functor inverts the selected morphisms. -/
noncomputable def inverts (C : SSet.QCat.{u}) (W : MorphismCollection C) :
    Inverts W (functor C W) :=
  (candidate C W).inverts

/-- The universal property of the chosen localization. -/
noncomputable def universal (C : SSet.QCat.{u}) (W : MorphismCollection C) :
    UniversalProperty W (functor C W) (inverts C W) :=
  (candidate C W).universal

end Localization

end SCTLocalizationSkeleton
