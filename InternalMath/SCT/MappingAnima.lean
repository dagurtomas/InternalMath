/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Maximal Kan core and mapping-anima skeleton

This file gives a small model-side scaffold for the workshop project on maximal Kan cores and
mapping anima. It is not intended to settle the mathematics locally. The declarations below split
that project into named API targets which can later be replaced by mathlib/infinity-cosmos results.

The intended semantics is:

* the maximal core of a quasicategory `C` is the subcomplex containing all vertices and exactly the
  equivalence edges;
* this subcomplex is a Kan complex;
* `Map(C,D)` is the maximal core of the functor quasicategory `Fun(C,D)`.

The `sorry`s here are project markers for human workshop work, not shortcuts for the SCT model.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SCTMappingAnimaSkeleton

universe u

namespace MaximalKanCore

/-- API target: the predicate saying that an edge of a simplicial set is an equivalence edge.

This should eventually be an alias for the upstream quasicategory equivalence-edge API, with
inverse-edge data and the usual two triangle witnesses.  It is kept abstract here so that the
workshop project can first agree on the API boundary.
-/
def EquivalenceEdge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) : Prop := by
  sorry

/-- API target: the maximal-core subcomplex of a quasicategory. -/
noncomputable def subcomplex (C : SSet.QCat.{u}) : C.obj.Subcomplex := by
  sorry

/-- The maximal core contains every vertex. -/
lemma mem_subcomplex_zero (C : SSet.QCat.{u}) (x : C.obj _⦋0⦌) :
    x ∈ (subcomplex C).obj (Opposite.op ⦋0⦌) := by
  sorry

/-- The one-simplices in the maximal core are exactly the equivalence edges. -/
lemma edge_mem_subcomplex_iff (C : SSet.QCat.{u}) {x y : C.obj _⦋0⦌}
    (e : SSet.Edge x y) :
    e.edge ∈ (subcomplex C).obj (Opposite.op ⦋1⦌) ↔ EquivalenceEdge e := by
  sorry

/-- API target: the maximal core is a Kan complex. -/
lemma kanComplex (C : SSet.QCat.{u}) :
    SSet.KanComplex ((subcomplex C : SSet.{u})) := by
  sorry

/-- The maximal core as a bundled quasicategory. -/
noncomputable def qcat (C : SSet.QCat.{u}) : SSet.QCat.{u} :=
  letI : SSet.KanComplex ((subcomplex C : SSet.{u})) := kanComplex C
  ⟨(subcomplex C : SSet.{u}), inferInstance⟩

/-- The inclusion of the maximal core into the ambient quasicategory. -/
noncomputable def incl (C : SSet.QCat.{u}) : qcat C ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (SSet.Subcomplex.ι (subcomplex C))

/-- API target: a map from a Kan complex into a quasicategory lands in the maximal core. -/
noncomputable def liftFromKan (A : SSet.{u}) [SSet.KanComplex A] (C : SSet.QCat.{u})
    (F : A ⟶ C.obj) : A ⟶ (qcat C).obj := by
  sorry

/-- The lift from a Kan complex composes with the core inclusion to the original map. -/
lemma liftFromKan_fac (A : SSet.{u}) [SSet.KanComplex A] (C : SSet.QCat.{u})
    (F : A ⟶ C.obj) :
    liftFromKan A C F ≫ (incl C).hom = F := by
  sorry

/-- The lift through the maximal core is unique as a map of simplicial sets. -/
lemma liftFromKan_uniq (A : SSet.{u}) [SSet.KanComplex A] (C : SSet.QCat.{u})
    (F : A ⟶ C.obj) (L : A ⟶ (qcat C).obj) (hL : L ≫ (incl C).hom = F) :
    L = liftFromKan A C F := by
  sorry

end MaximalKanCore

namespace MappingAnima

/-- Once a functor quasicategory has been supplied, the mapping anima is its maximal core. -/
noncomputable abbrev obj (FunCD : SSet.QCat.{u}) : SSet.{u} :=
  (MaximalKanCore.qcat FunCD).obj

/-- The mapping anima is Kan because it is a maximal core. -/
lemma kanComplex (FunCD : SSet.QCat.{u}) : SSet.KanComplex (obj FunCD) :=
  MaximalKanCore.kanComplex FunCD

/-- The inclusion `Map(C,D) → Fun(C,D)`, once `Fun(C,D)` has been supplied. -/
noncomputable def incl (FunCD : SSet.QCat.{u}) : MaximalKanCore.qcat FunCD ⟶ FunCD :=
  MaximalKanCore.incl FunCD

end MappingAnima

end SCTMappingAnimaSkeleton
