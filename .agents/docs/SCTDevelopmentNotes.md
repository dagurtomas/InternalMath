# SCT development notes for coding agents

These notes preserve detailed guidance that is useful for coding agents and maintainers, while the
public tutorial in `Docs/SCTTutorial.md` stays concise for human readers.

## Documentation split

- `Docs/` is for public, human-facing guides.
- `.agents/` is for detailed workflow notes, design warnings, and agent prompts.
- Avoid adding agent-oriented cautions to tutorials when a shorter factual sentence is enough.
- Keep this directory free of local paths, personal names, and tool-specific instructions.

A good public sentence is direct:

```text
Typed `lf_opaque` declarations become model-interface fields.
```

Longer operational advice belongs here.

## InternalLean declaration policy

SCT declarations should be classified before changing them:

1. **Primitive vocabulary**: basic language of the theory, such as `SCat`, `Anima`, `Functor`,
   `NatIso`, contextual-category vocabulary, and fibration witness vocabulary.
2. **Book axiom data**: assumptions or split universal-property packages matching the book's
   formulation.
3. **Book definitions**: declarations that should be `lf_def` or checked `internal def` when the
   needed data is available.
4. **Book theorems**: propositions that should become checked internal declarations.

`lf_opaque` introduces primitive vocabulary or axiom data. Typed `lf_opaque` declarations become
model-interface fields. A theorem-shaped gap should stay visible as an internal admission until it
is proved or until the surrounding representation is strengthened to match the book.

`lf_def` is for checked LF definitions inside a theory block. It should not add a new semantic field
when the construction is definable from previous data.

`internal def`, `internal theorem`, and `internal_defs where` add checked internal declarations from
the Lean namespace of the theory. Temporary admissions in these declarations remain visible to
`#lint_type_theory_sorries SCT`.

## Generated model interface

Changing the SCT specification can change the generated `SCTModel` interface. Before and after
interface-affecting edits, inspect the obligations with a scratch file such as:

```lean
import InternalMath.SCT.Spec

#print_model_obligations SCT
#check_model_obligations SCT
#print_model_template SCT as SCTModel
#lint_type_theory_sorries SCT
```

Expected current status:

- the SCT specification still has admitted internal declarations;
- `InternalMath/SCT/Model.lean` still has model placeholders;
- project scaffolds record real semantic gaps for future work.

Unexpected status:

- theorem-shaped SCT debt hidden as new primitive model fields without a book-level reason;
- semantic notions such as `NatIso`, `CatEquiv`, localization, fibration, or homotopy pullback
  replaced by vacuous data such as `True`, `PUnit`, or strict equality.

## Quasicategory model policy

The intended semantics is the infinity-category of small quasicategories, with:

- synthetic categories interpreted as small quasicategories;
- anima interpreted as Kan complexes;
- `Map(C,D)` interpreted by the maximal Kan complex of the functor quasicategory;
- natural isomorphisms interpreted as equivalences in functor quasicategories;
- directed univalence interpreted through the relevant universal fibration data.

Do not mark the semantic model complete until these assumptions are proved in Lean or recorded as
explicit external theorem assumptions with clear hypotheses.

## Current SCT project scaffolds

The current project files separate model gaps by topic:

- `InternalMath/SCT/IML/Model/FiniteShapes.lean`: checked finite-shape bookkeeping.
- `InternalMath/SCT/IML/Model/SegalComposition.lean`: Segal composition and the bridge between
  `[2]` and `Fun([1],[1])`.
- `InternalMath/SCT/IML/Model/IsoRezkModel.lean`: invertible-arrow and Rezk-equivalence scaffolding.
- `InternalMath/SCT/IML/Model/MappingAnima.lean`: maximal Kan cores and mapping anima.
- `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`: fibration-stable pullbacks and homotopy
  pullbacks.
- `InternalMath/SCT/IML/Model/Localization.lean`: inverting functors and localization.

When moving a gap out of `Model.lean`, put it in the project file that owns the mathematics and add
a docstring explaining what data remains.

## Subcategory and side-structure debt

Several Chapter 3 notions are currently primitive side structures:

```lean
LandsInObjectCollection
containsIdentities
closedUnderComposition
PreservesMorphismCollection
```

This staging is useful, but it lacks data needed for some internal proofs. For example,
`LandsInObjectCollection D C P F` should eventually expose that the induced map on cores factors
through the object-collection inclusion:

```text
coreCat D  --coreFunctor D C F-->  coreCat C
    \                                 ↑
     \                                |
      ------> objectCollectionCat C P --objectCollectionIncl C P--
```

Similarly, `PreservesMorphismCollection D C W F` should expose factorization data for the arrow map
induced by `F` through the selected morphism collection `W`.

Before adding a new primitive field, ask whether the missing fact should instead follow from an
explicit package already present in the book's formulation.

## Checks

Use narrow checks while editing:

```bash
lake env lean InternalMath/SCT/Spec.lean
lake env lean InternalMath/SCT/Model.lean
lake build InternalMath.SCT.Model
```

For documentation changes:

```bash
scripts/check_text_style.py --root Docs
scripts/check_text_style.py --root .agents
```

For substantial Lean changes:

```bash
lake build InternalMath
scripts/check_lean_line_lengths.py --max 100 --root InternalMath/SCT
git diff --check
```

A full text-style check may include ignored local planning files in some checkouts. When that is
unrelated to the task, check the changed public docs and `.agents` files directly.
