/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# Functor quasicategories

This file exposes the mathlib theorem that simplicial internal homs into quasicategories are again
quasicategories, and bundles the internal hom as the functor quasicategory used by the SCT model
scaffolds.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SCTFunctorQuasicategory

universe u

/-- The simplicial internal hom `D^C` is a quasicategory when `D` is a quasicategory. -/
lemma internalHomQuasicategory (C D : SSet.QCat.{u}) :
    SSet.Quasicategory ((ihom C.obj).obj D.obj) := by
  letI : SSet.Quasicategory D.obj := D.property
  infer_instance

/-- The functor quasicategory `Fun(C,D)`, realized as the simplicial internal hom. -/
def obj (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨(ihom C.obj).obj D.obj, internalHomQuasicategory C D⟩

end SCTFunctorQuasicategory
