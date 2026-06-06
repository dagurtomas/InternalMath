---
name: internalmath-docs
description: >-
  Use when editing README.md, Docs/*.md, .agents documentation, public examples, tutorial files, or
  repository-facing status notes in this project.
---

# InternalMath documentation workflow

Use this skill for documentation work in the `InternalMath` repository.

## Documentation split

- `README.md` and `Docs/` are public, human-facing docs.
- `.agents/` is for detailed agent and maintainer guidance.
- Public docs should explain what readers can do and where to start.
- Agent docs may include checklists, failure modes, trust-boundary warnings, and implementation
  conventions.

Keep `.agents/` tool-neutral:

- no local absolute paths;
- no private machine details;
- no instructions for one specific agent harness;
- no replacement for public docs that belong in `Docs/`.

## Public-doc style

- Keep beginner docs direct and concise.
- Prefer factual descriptions over operational cautions.
- Explain InternalLean terminology only as much as the reader needs for the page.
- For tutorials, show the common editor workflow rather than centering command-line checks.
- Mention limitations when they affect users, but move long operational guidance to
  `.agents/docs/SCTDevelopmentNotes.md` or a nearby `.agents` note.
- Workshop-facing docs should read as a stable guide for participants. Avoid edit-history wording
  such as "now", "formerly", "old", "stale", "migrated", or "no longer" unless writing a changelog
  or work log. Prefer direct state descriptions such as "These notions are admitted `syntax_def`
  packages."
- Do not put command-line acceptance checklists in workshop blueprints. Participants usually work in
  an editor and see whether the relevant Lean file compiles. Keep command-line checks in `.agents/`
  or handoff reports.
- Keep README links synchronized with major public docs.
- Preserve the README warning that most code in the repository was written by AI coding agents.

Good public wording is short and direct:

```text
Typed `lf_opaque` declarations become model-interface fields.
```

Longer guidance about when to use `lf_opaque`, how to classify theorem debt, and which checks to run
belongs in `.agents/`.

## Things to keep accurate

- The repository is experimental research-prototype material.
- `InternalMath/LambdaCalculus` is the complete example for the experimental scope.
- `InternalMath/SCT` is work in progress and has admitted internal declarations and model
  placeholders.
- `InternalMath.SCT.Spec` is the stable aggregate SCT import.
- `InternalMath/SCT/TutorialExercises.lean` is for exercises and is not imported by the root module.
- The SCT model uses `SSet.QCat` for synthetic categories and a full subcategory of Kan complexes
  for anima.
- Public descriptions of `lf_opaque`, `lf_def`, `internal def`, `internal theorem`, and
  `internal_defs where` should match InternalLean behavior.
- Expected warnings should be described as SCT/model debt, not as completed semantics.
- Public SCT docs should say the project implements the book's type theory and should avoid vague
  phrasing that weakens that goal.

## Checks

For docs-only edits:

```bash
scripts/check_text_style.py --root README.md
scripts/check_text_style.py --root Docs
scripts/check_text_style.py --root .agents
git diff --check
```

If Lean examples or tracked Lean tutorial files changed, also run an appropriate Lean check:

```bash
lake env lean InternalMath/SCT/TutorialExercises.lean
lake build InternalMath
```
