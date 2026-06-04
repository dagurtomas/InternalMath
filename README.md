# InternalMath

> [!WARNING]
> Most of the code in this repository was written by AI coding agents. Treat the implementation
> and documentation as research-prototype material that needs human review before reuse in
> high-assurance settings.

InternalMath is an experimental Lean 4 project for trying out
[InternalLean](https://github.com/dagurtomas/InternalLean) on mathematical type theories and their
models. The plan is to implement type theories with InternalLean, generate their Lean model
interfaces, and relate those interfaces to existing `mathlib` developments.

This repository is a research playground. APIs, declarations, and the exact statements of the
comparison theorems may change as InternalLean and the examples evolve.

## Current developments

### Simply typed lambda calculus

`InternalMath/LambdaCalculus` contains the currently complete example, for the present experimental
scope:

- an intrinsic simply typed lambda calculus with contexts, types, typed terms, explicit
  substitutions, products, unit, function types, definitional equality, and context
  representability;
- a generated InternalLean model interface;
- the interpretation of the calculus in any cartesian closed category;
- the syntactic cartesian closed category associated to any model;
- the Curry--Howard--Lambek comparison, including the equivalence from a cartesian closed category
  to the syntactic category of its interpreted STLC model and comparison data for arbitrary
  contexts.

See [`Docs/STLC.md`](Docs/STLC.md) for a guide to the files and declarations.

### Synthetic category theory

`InternalMath/SCT` is work in progress. It is an InternalLean implementation of the
type theory defined in the Cisinski--Cnossen--Nguyen--Walde **Synthetic Category Theory** book
project:

https://drive.google.com/file/d/1lKaq7watGGl3xvjqw9qHjm6SDPFJ2-0o/view

The goals are to implement this type theory, prove that quasicategories form a model, and let users
reason internally in the type theory from Lean. This is not yet complete. Many internal theorem
statements are currently admitted, and most model fields are still placeholders.

See [`Docs/SCT.md`](Docs/SCT.md) for the current status and expected warnings,
[`Docs/SCTTutorial.md`](Docs/SCTTutorial.md) for a tutorial on SCT's InternalLean syntax, and
[`InternalMath/SCT/TutorialExercises.lean`](InternalMath/SCT/TutorialExercises.lean) for beginner
exercises.

## Building

Use the Lean toolchain pinned by `lean-toolchain`.

```bash
lake build InternalMath
```

Focused checks for the current developments:

```bash
lake build InternalMath.LambdaCalculus.Basic
lake build InternalMath.LambdaCalculus.Model
lake build InternalMath.SCT.Model
```

The SCT build currently emits expected warnings about admitted InternalLean declarations and
placeholder `sorry`s in the model skeleton.

## Repository layout

- `InternalMath/LambdaCalculus/Basic.lean` — InternalLean specification of STLC.
- `InternalMath/LambdaCalculus/Model.lean` — generated model interface, CCC model, syntactic CCC,
  and Curry--Howard--Lambek comparison.
- `InternalMath/SCT/Spec.lean` — universe-polymorphic SCT specification organized around the book.
- `InternalMath/SCT/Model.lean` — generated SCT model interface and quasicategory/Kan-complex model
  skeleton.
- `Docs/` — guides for readers and users of this repo.

## License

InternalMath is released under the Apache 2.0 license, matching InternalLean. See
[`LICENSE`](LICENSE).
