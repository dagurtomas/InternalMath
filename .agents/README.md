# Shared agent context

This directory contains repository-specific guidance for AI coding agents. It is tracked so that
contributors can use the same project context across different agent tools.

Keep this directory tool-neutral:

- do not include local absolute paths;
- do not include personal names or private machine details;
- do not include instructions for one specific agent harness;
- keep public, human-facing documentation in `Docs/`.

## Contents

- `docs/SCTDevelopmentNotes.md` — detailed SCT/InternalLean guidance that is too verbose for the
  public tutorial.
- `skills/internalmath-docs/SKILL.md` — shared workflow notes for documentation edits.
- `skills/internalmath-sct/SKILL.md` — shared workflow notes for SCT edits.
- `skills/internallean-downstream/SKILL.md` — shared workflow notes for projects using
  InternalLean.

Public docs should be concise and reader-oriented. Agent notes can be more explicit about checks,
status conventions, and common failure modes.
