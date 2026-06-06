# IML workshop project index

This directory contains blueprints for IML workshop projects. Each blueprint explains the
mathematical goal, the relevant Lean files, dependencies between projects, and the expected shape of
a successful implementation.

Start with the SCT tutorial and exercise file if the InternalLean syntax is unfamiliar:

- [`Docs/SCTTutorial.md`](../SCTTutorial.md)
- [`InternalMath/SCT/TutorialExercises.lean`](../../InternalMath/SCT/TutorialExercises.lean)

For a smaller InternalLean warmup, open the local copy of the upstream intro exercises:

- [`InternalMath/IML/IntroExercises.lean`](../../InternalMath/IML/IntroExercises.lean)

Hints and worked solutions live in the InternalLean dependency checkout:

- [Intro exercise hints][intro-exercise-hints]
- [Intro exercise solutions][intro-exercise-solutions]

## Internal proof projects

Internal projects work inside the SCT object theory. They replace admitted internal declarations by
checked InternalLean definitions or proofs, without adding model fields.

### Strong surjectivity

- Blueprint: [Strong surjectivity blueprint][strong-surjectivity-internal]
- Suggested role: focused starter project.
- Dependency notes: uses core API already present in the specification; feeds the Fundamental
  Theorem project.

### Subcategories and full subcategories

- Blueprint: [subcategory and full subcategory blueprint][subcategory-internal]
- Suggested role: broad unlocker project.
- Dependency notes: basic side-structure and subcategory work can start from current Chapters 1--3;
  later full-subcategory equivalences use more core and Chapter 6 tools.

### Core and Axiom G

- Blueprint: [Core and Axiom G blueprint][core-axiom-g-internal]
- Suggested role: foundational core project.
- Dependency notes: independent of subcategories; improves later subcategory, strong-surjectivity,
  Fundamental Theorem, and universe work.

### Objectwise natural isomorphisms

- Blueprint: [objectwise natural isomorphism blueprint][objectwise-nat-iso-internal]
- Suggested role: interface design project.
- Dependency notes: requires careful declaration-order design around `NatIso`, components, and
  invertible arrows.

### Fundamental Theorem

- Blueprint: [Fundamental Theorem blueprint][fundamental-theorem-internal]
- Suggested role: capstone project.
- Dependency notes: uses strong surjectivity, core/Axiom G, objectwise natural isomorphisms, and
  subcategory results.

A good workshop sequence is to offer strong surjectivity as a small guided project, subcategories as
the main internal unlocker, and the Core/Axiom G or objectwise natural-isomorphism projects for
participants who want a deeper design problem. The Fundamental Theorem blueprint is best after its
supporting APIs are stable.

## Model construction projects

Model projects work in the quasicategory/Kan-complex interpretation of SCT. They usually require
human mathematical choices about which mathlib or infinity-cosmos APIs to use.

### Segal composition

- Blueprint: [Segal composition blueprint][segal-composition-model]
- Suggested role: foundational model project.
- Dependency notes: can start from finite shapes and horn fillers; later supports invertible-arrow
  unit comparisons.

### Maximal Kan cores and mapping anima

- Blueprint: [maximal Kan core and mapping anima blueprint][mapping-anima-model]
- Suggested role: foundational model project.
- Dependency notes: supplies maximal cores, equivalence edges, and mapping anima for several
  downstream projects.

### Fibration-stable pullbacks

- Blueprint: [fibration-stable pullbacks blueprint][fibration-pullbacks-model]
- Suggested role: phased model project.
- Dependency notes: strict-pullback and fibration-stability work can start separately;
  homotopy-pullback comparison uses mapping anima.

### Invertible arrows and Rezk equivalence

- Blueprint: [invertible arrows and Rezk equivalence blueprint][iso-rezk-model]
- Suggested role: downstream model project.
- Dependency notes: early edge adapters can start from finite shapes and inverse-edge APIs;
  `Iso(C)` and Rezk comparison use Segal composition and maximal-core work.

### Localization

- Blueprint: [localization blueprint][localization-model]
- Suggested role: downstream model project.
- Dependency notes: API audit and universal-property design can start separately; full localization
  uses mapping anima and equivalence-edge APIs.

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

[intro-exercise-hints]: ../../.lake/packages/InternalLean/Examples/IntroExercisesHints.lean
[intro-exercise-solutions]: ../../.lake/packages/InternalLean/Examples/IntroExercisesSolutions.lean
[strong-surjectivity-internal]: Internal/StrongSurjectivityInternalBlueprint.md
[subcategory-internal]: Internal/SubcategoryFullSubcategoryInternalBlueprint.md
[core-axiom-g-internal]: Internal/CoreAxiomGInternalBlueprint.md
[objectwise-nat-iso-internal]: Internal/ObjectwiseNatIsoInternalBlueprint.md
[fundamental-theorem-internal]: Internal/FundamentalTheoremInternalBlueprint.md
[segal-composition-model]: Model/SegalCompositionBlueprint.md
[mapping-anima-model]: Model/MaximalKanCoreMappingAnimaBlueprint.md
[fibration-pullbacks-model]: Model/FibrationStablePullbacksBlueprint.md
[iso-rezk-model]: Model/IsoRezkModelBlueprint.md
[localization-model]: Model/LocalizationBlueprint.md
