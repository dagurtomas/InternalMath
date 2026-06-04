# Synthetic category theory experiment

`InternalMath/SCT` is an experimental InternalLean implementation of the type theory defined in the
Cisinski--Cnossen--Nguyen--Walde **Synthetic Category Theory** book project:

https://drive.google.com/file/d/1lKaq7watGGl3xvjqw9qHjm6SDPFJ2-0o/view

The goals are to implement the type theory, prove that quasicategories form a model, and support
internal reasoning in Lean. This is work in progress.

## Files

- `InternalMath/SCT/Spec.lean` declares the type theory `SCT`.
- `InternalMath/SCT/Model.lean` generates `SCTModel` and contains the current quasicategory model
  skeleton.
- `Docs/SCTTutorial.md` introduces the SCT/InternalLean syntax.
- `InternalMath/SCT/TutorialExercises.lean` gives beginner exercises.

## Specification status

`Spec.lean` is organized around the vocabulary of the SCT book project, including:

- synthetic categories, functors, natural isomorphisms, and equivalences;
- anima/groupoids and groupoid cores;
- terminal, initial, product, coproduct, pullback, and functor-category constructions;
- subcategories, full subcategories, localizations, and exponentiable functors;
- context categories and contextual functors;
- cartesian, cocartesian, left, and right fibrations;
- limits, colimits, directed univalence, and universes.

The declaration is universe-polymorphic. For example, `SCat : Type (u+1)` and `Functor C D : Type u`
match the intended quasicategory model.

Many theorem-shaped internal declarations are currently admitted with `sorry`. These admissions are
visible to `#lint_type_theory_sorries SCT` and are expected to be replaced by checked internal
proofs or by axiom packages matching the book's formulation.

## Quasicategory model status

`Model.lean` currently provides concrete top-level carriers:

```lean
Anima := ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)
SCat := SSet.QCat.{u}
Functor := fun C D => C ⟶ D
```

Most remaining model fields are placeholders. The current carriers keep the intended
quasicategory/Kan-complex interpretation explicit while the full model is built.

## Expected warnings

The SCT files currently emit warnings about:

- admitted InternalLean declarations in the specification;
- `sorry` placeholders in the model skeleton and project scaffolds.

These warnings are known SCT/model debt.

## Useful checks

```bash
lake env lean InternalMath/SCT/Spec.lean
lake env lean InternalMath/SCT/Model.lean
lake build InternalMath.SCT.Model
```

## Where to start

Start with [`SCTTutorial.md`](SCTTutorial.md) for the syntax and exercises. Then read
`InternalMath/SCT/Spec/Prelude.lean` and the chapter file for the topic you want to study.
