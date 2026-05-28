# Synthetic category theory experiment

`InternalMath/SCT` is an experimental InternalLean implementation of the type theory defined in the
Cisinski--Cnossen--Nguyen--Walde **Synthetic Category Theory** book project:

https://drive.google.com/file/d/1lKaq7watGGl3xvjqw9qHjm6SDPFJ2-0o/view

The goals are to implement this type theory, prove that quasicategories form a model, and support
internal reasoning in the theory from Lean. This is work in progress.

## Files

- `InternalMath/SCT/Spec.lean` declares the type theory `SCT`.
- `InternalMath/SCT/Model.lean` generates `SCTModel` and contains a quasicategory/Kan-complex model
  skeleton.

## Specification status

`Spec.lean` is organized around the vocabulary of the SCT book project, including:

- synthetic categories, functors, natural isomorphisms, and equivalences;
- anima/groupoids and groupoid cores;
- terminal, initial, product, coproduct, pullback, and functor-category constructions;
- subcategories, full subcategories, localizations, and exponentiable functors;
- context categories and contextual functors;
- cartesian, cocartesian, left, and right fibrations;
- limits, colimits, directed univalence, and universes.

The declaration is universe-polymorphic. Sorts intended to be modeled by simplicial-set or
quasicategory-level data are annotated with explicit result universes, for example `SCat : Type
(u+1)` and `Functor C D : Type u`.

`Spec.lean` has no admitted InternalLean declarations. The current trust boundary is explicit:
book axioms and theorem packages that are not yet derived internally appear as source-facing
`lf_opaque` fields and therefore as model obligations. Over time, more of these fields should be
replaced by checked InternalLean declarations as the supporting representations are strengthened.

## Quasicategory model status

`Model.lean` currently provides concrete top-level carriers:

```lean
Anima := ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)
SCat := SSet.QCat.{u}
Functor := fun C D => C ⟶ D
```

Most remaining model fields are placeholders. The current concrete carriers keep the quasicategory
target in view while the full model is developed.

## Expected warnings

`Spec.lean` should elaborate without admitted-internal-declaration warnings. `Model.lean` still
emits warnings about `sorry` placeholders in the model skeleton.

These model warnings are known SCT/model debt. The current sanity check is that `SSet.QCat.{u}` and
the Kan-complex full subcategory elaborate at the expected universes.

## Useful checks

```bash
lake env lean InternalMath/SCT/Spec.lean
lake env lean InternalMath/SCT/Model.lean
lake build InternalMath.SCT.Model
```

## Reading the file

`Spec.lean` is best read as book-facing LF metadata rather than a polished public API. The comments
record chapter-level source context and, for several explicit theorem packages, explain what would
be needed to turn a model-facing obligation into a checked internal declaration.
