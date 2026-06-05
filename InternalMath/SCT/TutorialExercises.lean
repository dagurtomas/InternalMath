/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec

/-!
# SCT InternalLean exercises

Open this file in your editor and read it from top to bottom. It accompanies
`Docs/SCTTutorial.md` and gives small exercises in the InternalLean implementation of SCT.

How to use the exercises:

* Declarations named `exerciseXX_...` end in `sorry`. Replace each `sorry` with an internal proof
  term or internal tactic script.
* Some exercises ask you to inspect the SCT specification files and answer questions in comments.
* This file is not imported by `InternalMath.lean`, so the exercise admissions do not affect the
  main library unless you import this file yourself.

SCT is experimental. Several declarations used below expose admitted theorem or package debt.
-/

@[expose] public section

namespace SCT

/-!
## Worked example: using a side judgment rule

`isAnimaCat` is a custom judgment. The rule `anima_cat_is_anima` proves that the underlying
category of a primitive anima is an anima-category.
-/

internal def example01_anima_cat (A : Anima) : isAnimaCat (animaCat A) := by
  exact anima_cat_is_anima A

/-!
## Worked example: object notation

`Obj C` is an abbreviation for `Functor terminalCat C`. The internal proof term below is just the
object itself, viewed through the abbreviation.
-/

internal def example02_object_as_functor (C : SCat) (x : Obj C) : Functor terminalCat C := by
  exact x

/-!
## Exercise 1: repeat the side judgment rule

Fill the proof using `anima_cat_is_anima`.
-/

internal def exercise01_anima_cat (A : Anima) : isAnimaCat (animaCat A) := by
  sorry

/-!
## Exercise 2: use a rule with parameters

Use `equiv_to_anima_is_anima`. The parameter `e` is equivalence data from `C` to the underlying
category of the anima `A`.
-/

internal def exercise02_equiv_to_anima
    (C : SCat) (A : Anima) (e : CatEquiv C (animaCat A)) : isAnimaCat C := by
  sorry

/-!
## Exercise 3: unfold object notation mentally

The target is definitionally the same kind of thing as the hypothesis `x`.
-/

internal def exercise03_object_as_functor (C : SCat) (x : Obj C) : Functor terminalCat C := by
  sorry

/-!
## Exercise 4: internal functions

The target `(x : Obj C) → Obj C` is InternalLean's structural function type. Use `intro` to bring
an internal object into the context, then return it.
-/

internal def exercise04_identity_on_objects (C : SCat) : (x : Obj C) → Obj C := by
  sorry

/-!
## Exercise 5: constant functors

Read `constantFunctor` in `Spec/Chapter1/BasicConstructions.lean`, then use it to build a functor
from `C` to `D` with constant value `x`.
-/

internal def exercise05_constant_functor (C : SCat) (D : SCat) (x : Obj D) : Functor C D := by
  sorry

/-!
## Exercise 6: compatibility between objects and terminal functors

Use the checked LF definition `objectFunctor`.
-/

internal def exercise06_object_functor (C : SCat) (x : Obj C) : Functor terminalCat C := by
  sorry

/-!
## Exercise 7: functors as objects of a functor category

Find `functorObject` in `Spec/Chapter1/BasicConstructions.lean`, then use it here.
-/

internal def exercise07_functor_object (C : SCat) (D : SCat) (F : Functor C D) :
    Obj (funCat C D) := by
  sorry

/-!
## Exercise 8: lifting through the core

Find `coreLift` in `Spec/Chapter2/Cores.lean`. It lifts an anima-indexed family of objects of `C`
through the core inclusion.
-/

internal def exercise08_core_lift (A : Anima) (C : SCat) (F : Functor (animaCat A) C) :
    Functor (animaCat A) (coreCat C) := by
  sorry

/-!
## Exercise 9: product pairing

Use `prodPair` to assemble two functors with common source into a functor to the product category.
-/

internal def exercise09_pair_functor (Γ : SCat) (C : SCat) (D : SCat)
    (F : Functor Γ C) (G : Functor Γ D) : Functor Γ (prodCat C D) := by
  sorry

/-!
## Exercise 10: changing across an internal definition

The first declaration is complete. In the second one, use `change` to replace the target with the
unfolded target, then use `terminalProjection`.
-/

internal def exercise10_terminal_alias : SCat := terminalCat

internal def exercise10_change_alias : Functor exercise10_terminal_alias terminalCat := by
  sorry

/-!
## Exercise 11: batched internal declarations

`internal_defs where` registers declarations in source order. Fill the first declaration with a
category and the second with a functor from that category to `terminalCat`.
-/

internal_defs where
  def exercise11_batch_category : SCat := by
    sorry
  def exercise11_batch_projection : Functor exercise11_batch_category terminalCat := by
    sorry

/-!
## Exercise 12: read a package and its projections

Open `Spec/Chapter2/Cores.lean` and inspect `coreUniversalPackage` together with these checked
projections:

* `coreInclEmbedding`
* `coreLiftPackage`
* `coreLift`
* `coreLiftBeta`
* `coreLiftUniq`

Questions:

1. Which projection is just the first projection of `coreUniversalPackage`?
2. Which projections unpack nested Sigma fields?
3. Which projections produce functors, and which produce natural-isomorphism data?
-/

/-!
## Exercise 13: inspect subcategory package debt

Open `Spec/Chapter3/Subcategories.lean` and find the declarations below:

* `LandsInObjectCollection`
* `containsIdentities`
* `closedUnderComposition`
* `PreservesMorphismCollection`

Questions:

1. Which ones are marked with `syntax_sort_role ... : side_structure`?
2. What concrete data would you want to unpack from `LandsInObjectCollection`?
3. What concrete data would you want to unpack from `PreservesMorphismCollection`?

These declarations are admitted `syntax_def` packages. Checked package bodies should expose the
factorization data needed by the subcategory proofs.
-/

/-!
Try uncommenting these commands after filling the exercises. The lint command reports SCT theorem
debt; the exercise admissions should disappear from its output.
-/

-- #lint_type_theory_sorries SCT
-- #print_internal_registration_profile SCT
-- #check_theory SCT

end SCT
