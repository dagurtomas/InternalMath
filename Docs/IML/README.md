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
- Dependencies: can start immediately.
- Later projects: [Fundamental Theorem](#fundamental-theorem).

### Subcategories and full subcategories

- Blueprint: [subcategory and full subcategory blueprint][subcategory-internal]
- Suggested role: broad unlocker project.
- Dependencies: can start immediately.
- Later parts also depend on [Core and Axiom G](#core-and-axiom-g) or
  [Fundamental Theorem](#fundamental-theorem).

### Core and Axiom G

- Blueprint: [Core and Axiom G blueprint][core-axiom-g-internal]
- Suggested role: foundational core project.
- Dependencies: can start immediately.
- Later projects: [Subcategories and full subcategories](#subcategories-and-full-subcategories),
  [Strong surjectivity](#strong-surjectivity), and
  [Fundamental Theorem](#fundamental-theorem).

### Objectwise natural isomorphisms

- Blueprint: [objectwise natural isomorphism blueprint][objectwise-nat-iso-internal]
- Suggested role: interface design project.
- Dependencies: can start immediately; first choose the declaration-order design.
- Later projects: [Fundamental Theorem](#fundamental-theorem) and
  [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence).

### Fundamental Theorem

- Blueprint: [Fundamental Theorem blueprint][fundamental-theorem-internal]
- Suggested role: capstone project.
- Dependencies: [Strong surjectivity](#strong-surjectivity),
  [Core and Axiom G](#core-and-axiom-g),
  [Objectwise natural isomorphisms](#objectwise-natural-isomorphisms), and
  [Subcategories and full subcategories](#subcategories-and-full-subcategories).

A good workshop sequence is to offer strong surjectivity as a small guided project, subcategories as
the main internal unlocker, and the Core/Axiom G or objectwise natural-isomorphism projects for
participants who want a deeper design problem. The Fundamental Theorem blueprint is best after its
supporting APIs are stable.

## Model construction projects

Model projects work in the quasicategory/Kan-complex interpretation of SCT. They usually require
human mathematical choices about which mathlib or infinity-cosmos APIs to use.

### Functor quasicategory bridge

- Blueprint: [functor quasicategory bridge blueprint][functor-quasicategory-bridge-model]
- Suggested role: upstream mathlib API project.
- Dependencies: mathlib PR #40243 for internal-hom quasicategory closure.
- Later projects: [Segal composition](#segal-composition),
  [Maximal Kan cores and mapping anima](#maximal-kan-cores-and-mapping-anima),
  [Fibration-stable pullbacks](#fibration-stable-pullbacks),
  [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence), and
  [Localization](#localization).

### Segal composition

- Blueprint: [Segal composition blueprint][segal-composition-model]
- Suggested role: foundational model project.
- Dependencies: can start immediately; comparison-data phases use the
  [functor quasicategory bridge](#functor-quasicategory-bridge).
- Later projects: [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence).

### Maximal Kan cores and mapping anima

- Blueprint: [maximal Kan core and mapping anima blueprint][mapping-anima-model]
- Suggested role: foundational model project.
- Dependencies: can start immediately; mapping-anima phases use the
  [functor quasicategory bridge](#functor-quasicategory-bridge).
- Later projects: [Fibration-stable pullbacks](#fibration-stable-pullbacks),
  [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence), and
  [Localization](#localization).

### Fibration-stable pullbacks

- Blueprint: [fibration-stable pullbacks blueprint][fibration-pullbacks-model]
- Suggested role: phased model project.
- Dependencies: can start immediately.
- Later parts depend on [Maximal Kan cores and mapping anima](#maximal-kan-cores-and-mapping-anima),
  [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence), and the
  anticipated Reedy homotopy-limit API.

### Invertible arrows and Rezk equivalence

- Blueprint: [invertible arrows and Rezk equivalence blueprint][iso-rezk-model]
- Suggested role: downstream model project.
- Dependencies: early edge-adapter parts can start immediately.
- Later parts depend on [Segal composition](#segal-composition) and
  [Maximal Kan cores and mapping anima](#maximal-kan-cores-and-mapping-anima).

### Localization

- Blueprint: [localization blueprint][localization-model]
- Suggested role: downstream model project.
- Dependencies: early API-design parts can start immediately.
- Later parts depend on [Maximal Kan cores and mapping anima](#maximal-kan-cores-and-mapping-anima).
- Later parts also use
  [Invertible arrows and Rezk equivalence](#invertible-arrows-and-rezk-equivalence).

A good model-project sequence is to start the functor-quasicategory bridge, Segal composition, and
maximal cores/mapping anima first. The early phases of fibration-stable pullbacks can run in
parallel. Iso/Rezk and localization become more productive once the foundational projects provide
stable APIs.

## Choosing a project

- Choose an internal project if you want to work internally in SCT to work towards completing the
  "declaration" of SCT.
- Choose a model project if you want to work on the quasicategory semantics and work towards proving
  that there is a model for SCT (quasicategories).

[intro-exercise-hints]: ../../.lake/packages/InternalLean/Examples/IntroExercisesHints.lean
[intro-exercise-solutions]: ../../.lake/packages/InternalLean/Examples/IntroExercisesSolutions.lean
[strong-surjectivity-internal]: Internal/StrongSurjectivityInternalBlueprint.md
[subcategory-internal]: Internal/SubcategoryFullSubcategoryInternalBlueprint.md
[core-axiom-g-internal]: Internal/CoreAxiomGInternalBlueprint.md
[objectwise-nat-iso-internal]: Internal/ObjectwiseNatIsoInternalBlueprint.md
[fundamental-theorem-internal]: Internal/FundamentalTheoremInternalBlueprint.md
[functor-quasicategory-bridge-model]: Model/FunctorQuasicategoryBridgeBlueprint.md
[segal-composition-model]: Model/SegalCompositionBlueprint.md
[mapping-anima-model]: Model/MaximalKanCoreMappingAnimaBlueprint.md
[fibration-pullbacks-model]: Model/FibrationStablePullbacksBlueprint.md
[iso-rezk-model]: Model/IsoRezkModelBlueprint.md
[localization-model]: Model/LocalizationBlueprint.md
