# Synthetic category theory experiment

`InternalMath/SCT` is an experimental InternalLean implementation of the type theory defined in the
Cisinski--Cnossen--Nguyen--Walde **Synthetic Category Theory** book project:

https://drive.google.com/file/d/1lKaq7watGGl3xvjqw9qHjm6SDPFJ2-0o/view

The goals are to implement the type theory, prove that quasicategories form a model, and support
internal reasoning in Lean. This is work in progress.

## Files

- `InternalMath/SCT/Spec.lean` is the stable aggregate import for the SCT specification.
- `InternalMath/SCT/Spec/Prelude.lean` starts the `SCT` type theory.
- `InternalMath/SCT/Spec/Chapter*/...` contains the chapter and topic extensions.
- `InternalMath/SCT/Model.lean` generates `SCTModel` and contains the quasicategory model skeleton.
- `InternalMath/SCT/IML/Model/` contains Lean scaffolds for SCT model construction projects.
- `Docs/IML/Internal/` contains workshop blueprints for internal SCT proof projects.
- `Docs/IML/Model/` contains workshop blueprints for model construction projects.
- `Docs/SCTTutorial.md` introduces the SCT/InternalLean syntax.
- `InternalMath/SCT/TutorialExercises.lean` gives beginner exercises and is not imported by the
  root library.

## Specification status

`Spec.lean` is organized around the vocabulary of the SCT book project, including:

- synthetic categories, functors, natural transformations, natural isomorphisms, and equivalences;
- anima/groupoids and groupoid cores;
- terminal, initial, product, coproduct, pullback, and functor category constructions;
- subcategories, full subcategories, localizations, and exponentiable functors;
- context categories and contextual functors;
- cartesian, cocartesian, left, and right fibrations;
- limits, colimits, directed univalence, and universes.

The declaration is universe-polymorphic. For example, `SCat : Type (u+1)` and `Functor C D : Type u`
match the intended quasicategory model.

Primitive vocabulary such as `SCat`, `Anima`, `Functor`, and `NatTrans` is declared with
`syntax_sort` or `lf_opaque`. Package-shaped notions use `syntax_abbrev` or `syntax_def` so that
their data can be projected in internal proofs. Some package bodies are checked, including
`InvertibleMorphismData`, `LeftAdjointSection`, and `RightAdjointSection`. Other packages are
admitted design debt, including the Chapter 3 side structures, `ObjectwiseNatIsoData`, `Adjunction`,
and the general limit/colimit packages.

Many internal theorem statements are admitted with `sorry`. These admissions are visible to
`#lint_type_theory_sorries SCT` and are expected to be replaced by checked internal proofs or by
axiom packages matching the book's formulation.

## Quasicategory model status

`Model.lean` interprets the basic SCT carriers with mathlib's APIs for simplicial sets:

```lean
Anima := SSet.Kan.{u}
SCat := SSet.QCat.{u}
Functor := fun C D => C ⟶ D
```

The model implements a substantial first layer:

- anima categories, terminal and initial categories, products, finite shapes, and nerves of ordinary
  categories;
- strict bicategorical natural transformations and natural isomorphisms for quasicategories;
- bicategorical adjunction data for the Chapter 5 adjunction package;
- several functor category operations through simplicial internal homs;
- strict comparison helpers such as `initialStrict` and `qcatCatEquivOfIso`.

The functor category carrier uses the simplicial internal hom. The open API gap there is a theorem
that the internal hom from a quasicategory `C` to a quasicategory `D` is again a quasicategory.

The open model projects are concentrated in higher universal properties and later SCT structure:
objectwise components of natural transformations, product and coproduct uniqueness, homotopy
pullbacks, Segal composition, Rezk equivalences, mapping anima, subcategories, localization,
contexts, fibrations, limits, colimits, and universes.

## Expected warnings

The SCT files emit expected warnings about SCT/model debt:

- admitted InternalLean declarations in the specification;
- admitted `syntax_def` package bodies;
- `sorry` placeholders in the model skeleton and model project scaffolds;
- one temporary generated model field, `leftAdjointSectionFunctor`, needed by later Chapter 5 and
  Chapter 7 obligations.

A useful baseline is:

```lean
import InternalMath.SCT.Spec
#lint_type_theory_sorries SCT
#check_model_obligations SCT
```

The linter reports 87 admitted internal declarations. The model obligation check reports the generic
LF model backend status. `lake build InternalMath.SCT.Model` succeeds with the expected warnings.

## Useful checks

```bash
lake env lean InternalMath/SCT/Spec.lean
lake env lean InternalMath/SCT/Model.lean
lake build InternalMath.SCT.Model
```

## Where to start

Start with [`SCTTutorial.md`](SCTTutorial.md) and
[`InternalMath/SCT/TutorialExercises.lean`](../InternalMath/SCT/TutorialExercises.lean). For an
internal proof project, choose a focused blueprint under [`Docs/IML/Internal/`](IML/Internal/). For
a model project, choose a focused blueprint under [`Docs/IML/Model/`](IML/Model/).

- [Subcategory and full subcategory blueprint](IML/Internal/SubcategoryFullSubcategoryInternalBlueprint.md)
- [Strong surjectivity blueprint](IML/Internal/StrongSurjectivityInternalBlueprint.md)
- [Core and Axiom G blueprint](IML/Internal/CoreAxiomGInternalBlueprint.md)
- [Objectwise natural isomorphism blueprint](IML/Internal/ObjectwiseNatIsoInternalBlueprint.md)
- [Fundamental Theorem blueprint](IML/Internal/FundamentalTheoremInternalBlueprint.md)
