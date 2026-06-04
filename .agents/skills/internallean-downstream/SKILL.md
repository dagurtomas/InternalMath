---
name: internallean-downstream
description: >-
  Use when editing InternalLean object-theory declarations, generated model interfaces, internal
  proofs, or transports in a downstream Lean project.
---

# InternalLean downstream workflow

Use this skill in Lean projects that depend on InternalLean, including InternalMath.

## Locate InternalLean

Downstream projects usually vendor InternalLean through Lake:

```text
.lake/packages/InternalLean/
```

Useful files there include:

- `InternalLean/Basic.lean`: low-level LF and kernel layer.
- `InternalLean/DSL.lean`: object-expression and declaration syntax structures.
- `InternalLean/Registry.lean`: registries, admissions, transports, and metadata.
- `InternalLean/LFElab.lean`: LF elaboration, checking, and replay lowering.
- `InternalLean/Registration.lean`: theory declaration and internal-definition commands.
- `InternalLean/Diagnostics.lean`: print, lint, and inspection commands.
- `InternalLean/ModelInterface.lean`: generated model obligations and templates.
- `InternalLean/ModelTransport.lean`: generated model transports.
- `Docs/*.md`: InternalLean user documentation.
- `Examples/*.lean` and `InternalLeanTest/*.lean`: examples and regression tests.

Read the package files when behavior is unclear.

## Core concepts

- InternalLean is infrastructure for user-declared object type theories.
- Well-typed object-language terms are not the same thing as Lean terms.
- Judgmental equality is object-theory data, not Lean equality.
- Internal proofs inhabit judgments or types declared by the object theory.
- Scope, binders, substitution, and capture avoidance are trust-boundary details.
- Generated model interfaces should expose semantic obligations instead of hiding missing proofs.

## Admissions policy

Distinguish three common cases:

1. **Source axiom data**: use `lf_opaque` or rules with a clear mathematical reason.
2. **Source definitions**: use `lf_def` or checked `internal def`.
3. **Source theorems**: prove with checked internal declarations when possible.

A temporary `internal def ... := sorry` can be useful during development. It should remain visible
to the relevant linter and should not quietly become a permanent model-provider field.

## Generated interface workflow

When changing a theory declaration, inspect the generated interface before and after the change:

```lean
#print_model_obligations T
#check_model_obligations T
#print_model_interface T as TModel
#print_model_template T as TModel
#lint_type_theory_sorries T
```

For generated transports:

```lean
#print_model_transport_status T for TModel
#print_model_transport_signature T someDecl for TModel
#print_model_transports T for TModel
generate_model_transport T someDecl for TModel
generate_model_transports T only someDecl anotherDecl for TModel
```

Run generation commands from a stable namespace unless the command documentation says otherwise.

## Checks

Use the narrowest check that covers the edit:

```bash
lake env lean path/to/File.lean
lake build Project.Module
```

If the InternalLean package itself is edited, run relevant package checks as well, for example:

```bash
cd .lake/packages/InternalLean
lake build InternalLean.Command
lake build InternalLeanTest
```

## Performance notes

Large object theories can expose InternalLean performance issues. If a change causes a large
slowdown, minimize the reproducer and identify whether the cost is in syntax expansion, telescope
elaboration, replay validation, obligation generation, pretty-printing, transport search, or
unfolding.
