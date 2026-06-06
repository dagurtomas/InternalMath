# IML workshop project index

This directory contains blueprints for SCT workshop projects. Each blueprint explains the
mathematical goal, the relevant Lean files, dependencies between projects, and the expected shape of
a successful implementation.

Start with the SCT tutorial and exercise file if the InternalLean syntax is unfamiliar:

- [`Docs/SCTTutorial.md`](../SCTTutorial.md)
- [`InternalMath/SCT/TutorialExercises.lean`](../../InternalMath/SCT/TutorialExercises.lean)

## Internal proof projects

Internal projects work inside the SCT object theory. They replace admitted internal declarations by
checked InternalLean definitions or proofs, without adding model fields.

| Project | Blueprint | Suggested role | Dependency notes |
|---|---|---|---|
| Strong surjectivity | [`StrongSurjectivityInternalBlueprint.md`](Internal/StrongSurjectivityInternalBlueprint.md) | Focused starter project | Uses core API already present in the specification; feeds the Fundamental Theorem project. |
| Subcategories and full subcategories | [`SubcategoryFullSubcategoryInternalBlueprint.md`](Internal/SubcategoryFullSubcategoryInternalBlueprint.md) | Broad unlocker project | Basic side-structure and subcategory work can start from current Chapters 1--3; later full-subcategory equivalences use more core and Chapter 6 tools. |
| Core and Axiom G | [`CoreAxiomGInternalBlueprint.md`](Internal/CoreAxiomGInternalBlueprint.md) | Foundational core project | Independent of subcategories; improves later subcategory, strong-surjectivity, Fundamental Theorem, and universe work. |
| Objectwise natural isomorphisms | [`ObjectwiseNatIsoInternalBlueprint.md`](Internal/ObjectwiseNatIsoInternalBlueprint.md) | Interface design project | Requires careful declaration-order design around `NatIso`, components, and invertible arrows. |
| Fundamental Theorem | [`FundamentalTheoremInternalBlueprint.md`](Internal/FundamentalTheoremInternalBlueprint.md) | Capstone project | Uses strong surjectivity, core/Axiom G, objectwise natural isomorphisms, and subcategory results. |

A good workshop sequence is to offer strong surjectivity as a small guided project, subcategories as
the main internal unlocker, and the Core/Axiom G or objectwise natural-isomorphism projects for
participants who want a deeper design problem. The Fundamental Theorem blueprint is best after its
supporting APIs are stable.

## Model construction projects

Model projects work in the quasicategory/Kan-complex interpretation of SCT. They usually require
human mathematical choices about which mathlib or infinity-cosmos APIs to use.

| Project | Blueprint | Suggested role | Dependency notes |
|---|---|---|---|
| Segal composition | [`SegalCompositionBlueprint.md`](Model/SegalCompositionBlueprint.md) | Foundational model project | Can start from finite shapes and horn fillers; later supports invertible-arrow unit comparisons. |
| Maximal Kan cores and mapping anima | [`MaximalKanCoreMappingAnimaBlueprint.md`](Model/MaximalKanCoreMappingAnimaBlueprint.md) | Foundational model project | Supplies maximal cores, equivalence edges, and mapping anima for several downstream projects. |
| Fibration-stable pullbacks | [`FibrationStablePullbacksBlueprint.md`](Model/FibrationStablePullbacksBlueprint.md) | Phased model project | Strict-pullback and fibration-stability work can start separately; homotopy-pullback comparison uses mapping anima. |
| Invertible arrows and Rezk equivalence | [`IsoRezkModelBlueprint.md`](Model/IsoRezkModelBlueprint.md) | Downstream model project | Early edge adapters can start from finite shapes and inverse-edge APIs; `Iso(C)` and Rezk comparison use Segal composition and maximal-core work. |
| Localization | [`LocalizationBlueprint.md`](Model/LocalizationBlueprint.md) | Downstream model project | API audit and universal-property design can start separately; full localization uses mapping anima and equivalence-edge APIs. |

A good model-project sequence is to start Segal composition and maximal cores/mapping anima first.
The early phases of fibration-stable pullbacks can run in parallel. Iso/Rezk and localization become
more productive once the foundational projects provide stable APIs.

## Choosing a project

- Choose an internal project to work in SCT's object language and reduce admitted internal
  declarations.
- Choose a model project to work on the quasicategory semantics and mathlib-facing adapters.
- Prefer projects whose dependency notes match the available participants: focused projection tasks
  for first InternalLean work, and API-design or theorem-packaging tasks for participants with more
  quasicategory background.
