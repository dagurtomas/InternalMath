---
name: internalmath-sct
description: >-
  Use when editing InternalMath/SCT, SCT documentation, SCT model obligations, or SCT project
  scaffolds.
---

# InternalMath SCT workflow

Use this skill for work on the Synthetic Category Theory development under `InternalMath/SCT` and
its public documentation under `Docs/`.

## Core goal

`InternalMath.SCT` implements the type theory from the Cisinski--Cnossen--Nguyen--Walde Synthetic
Category Theory book project. Prefer declarations and structures that match the book's formulation,
even when that requires more InternalLean support or a longer refactor.

## Main files

- `InternalMath/SCT/Spec.lean`: stable aggregate import for the SCT specification.
- `InternalMath/SCT/Spec/Prelude.lean`: initial theory declaration.
- `InternalMath/SCT/Spec/Chapter*/...`: staged chapter/topic extensions.
- `InternalMath/SCT/Model.lean`: generated model interface and quasicategory/Kan-complex model
  skeleton.
- `InternalMath/SCT/IML/Model/FiniteShapes.lean`: checked finite-shape API.
- `InternalMath/SCT/IML/Model/SegalComposition.lean`: Segal composition and the
  `[2]`/`Fun([1],[1])` bridge.
- `InternalMath/SCT/IML/Model/IsoRezkModel.lean`: invertible-arrow and Rezk-equivalence scaffold.
- `InternalMath/SCT/IML/Model/MappingAnima.lean`: maximal-Kan-core and mapping-anima scaffold.
- `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`: fibration-stable pullback scaffold.
- `InternalMath/SCT/IML/Model/Localization.lean`: inverting-functor and localization scaffold.
- `Docs/SCT.md` and `Docs/SCTTutorial.md`: concise human-facing docs.
- `.agents/docs/SCTDevelopmentNotes.md`: detailed agent-facing SCT guidance.

## Admissions and primitives

Classify each SCT gap before changing it:

1. primitive vocabulary;
2. book axiom data;
3. book definition;
4. book theorem.

Use `lf_opaque` for primitive vocabulary or axiom data. Typed `lf_opaque` declarations become model
fields. Do not turn theorem-shaped debt into new primitive fields unless the book treats the data as
axiomatic.

Use `lf_def` or checked internal definitions for derived constructions. Keep theorem debt visible to
`#lint_type_theory_sorries SCT` until it is proved or represented by a book-faithful axiom package.

## Semantic model policy

Do not fake semantic structures with strict equality, `True`, `PUnit`, or empty placeholder data.
This applies especially to:

- `NatIso` and natural transformations;
- `CatEquiv`;
- equivalence edges and maximal cores;
- fibrations and localization;
- pullbacks and homotopy pullbacks;
- universe and directed-univalence witnesses.

Placeholder structures should state the mathematical data to supply.

## Workflow

1. Inspect the relevant specification, model, scaffold, or doc files.
2. If changing the specification or model interface, inspect generated obligations:
   ```lean
   import InternalMath.SCT.Spec

   #print_model_obligations SCT
   #check_model_obligations SCT
   #print_model_template SCT as SCTModel
   #lint_type_theory_sorries SCT
   ```
3. Keep `InternalMath.SCT.Spec` as the public aggregate import.
4. Keep tutorial exercises out of `InternalMath.lean` unless they are meant to become library code.
5. Move model gaps into topic-specific project files only when the new location states the real
   mathematical obligation.
6. Keep public docs concise and human-oriented; put verbose agent guidance in `.agents/`.
7. Workshop-facing docs should present the state participants should use, not repository edit
   history. Avoid wording such as "now", "formerly", "old", "stale", "migrated", or "no longer"
   except in changelogs/work logs.

## Checks

For small SCT edits:

```bash
lake env lean InternalMath/SCT/Spec.lean
lake env lean InternalMath/SCT/Model.lean
```

For substantial SCT edits:

```bash
lake build InternalMath.SCT.Model
scripts/check_lean_line_lengths.py --max 100 --root InternalMath/SCT
git diff --check
```

For docs-only edits:

```bash
scripts/check_text_style.py --root Docs
scripts/check_text_style.py --root .agents
git diff --check
```
