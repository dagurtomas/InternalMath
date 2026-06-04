# Fibration-stable pullbacks and homotopy pullbacks blueprint

Status: synced with current fibration-pullback scaffold, 2026-06-03.

Scope: this note expands the project around `pullbackCat`, base-change of fibrations, and directed
pullbacks in `InternalMath/SCT/Model.lean`.  It is written for human workshop participants.  The
companion Lean scaffold is `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`.

## Short version

The general SCT field

```text
pullbackCat C D E F G
```

should be interpreted as an ∞-categorical/homotopy pullback in `Cat_∞`.  A strict simplicial-set
pullback

```text
C ×_E D
```

is a valid model only under hypotheses such as: one leg of the cospan is an inner fibration, or the
strict pullback has been shown to represent the derived/homotopy pullback.  The workshop project is
to build this fibration-stable strict-pullback API and document how it can, and cannot yet, close
SCT model fields.

Current model note: natural transformations are bicategorical 2-cells in mathlib's strict
bicategory of quasicategories. The fibration-pullback scaffold still uses strict equality for the
special strict cone where a pullback square commutes on the nose; the eventual homotopy-pullback
package should expose coherent `NatIso` comparison data for general SCT pullbacks.

## Why this is a human workshop project

This project is human-led because it requires semantic choices:

- which notion of fibration should model the book's `IsofibrationWitness`;
- how to relate inner fibrations of simplicial sets to isofibrations of quasicategories;
- whether the model should choose strict pullbacks only under fibrancy hypotheses or use a general
  replacement/fibrant-replacement construction;
- how directed/lax pullbacks in Chapter 5 relate to strict pullbacks and arrow-category pullbacks;
- which parts should be upstreamed to mathlib/infinity-cosmos rather than encoded locally.

Agents can help with typed wrappers, projection lemmas, and strict β-rules after the semantic target
is fixed.

## Existing SCT declarations involved

Chapter 1 pullbacks:

- `pullbackCat`;
- `pullbackPr1`, `pullbackPr2`;
- `pullbackComm`;
- `pullbackLift`;
- `pullbackBeta1`, `pullbackBeta2`;
- `pullbackUniq`, `pullbackEta`.

Derived from these:

- `fiberCat` and its projections;
- object-level hom categories `objectHomCat`;
- natural-transformation endpoint fibers;
- composition and square-shape objects.

Chapter 5 fibration/base-change fields:

- `IsofibrationWitness` / `Fibration`;
- `directedPullbackCat`, `directedPullbackPr1`, `directedPullbackPr2`,
  `directedPullbackArrow`;
- `directedEval0`, `directedEval1`;
- `sourceFibration`, `targetFibration`;
- `baseChangeFibration`;
- `baseChangeCartesian`, `baseChangeCocartesian`;
- `directedPullbackMapOverBase`;
- later cartesian/cocartesian functor and Beck-Chevalley fields.

## Mathematical targets

### Target A: choose the fibration notion

Pick or wrap the notion of fibration that makes strict pullbacks homotopically meaningful.

Candidates:

1. **inner fibration** of simplicial sets: right lifting against all inner horn inclusions;
2. **categorical fibration/isofibration** in the Joyal model structure;
3. an infinity-cosmos isofibration API, if available upstream;
4. a book-specific `IsofibrationWitness` adapter for synthetic categories.

Expected first API shape:

```lean
innerHornInclusions : MorphismProperty SSet
InnerFibration (p : E ⟶ B) : Prop := innerHornInclusions.rlp p
```

The current scaffold defines this local wrapper directly because this mathlib checkout does not
appear to have a named `InnerFibration`.  A later pass can replace it by an upstream name and add a
theorem connecting it to the book's `IsofibrationWitness` interpretation.

Design question: the model's Chapter 5 `Fibration` is the book's isofibration condition, while
strict-pullback stability of quasicategories is often stated for inner fibrations.  Decide whether
`IsofibrationWitness` should be stronger than inner fibration, or whether base-change stability uses
a separate theorem from categorical fibrations to inner fibrations.

### Target B: strict pullbacks of quasicategories under a fibration hypothesis

Prove or import:

```lean
quasicategoryOfRightInnerFibration
quasicategoryOfLeftInnerFibration
```

Mathematical statement:

If `C`, `D`, and `E` are quasicategories and one leg of `C → E ← D` is an inner fibration, then the
strict simplicial-set pullback `C ×_E D` is a quasicategory.

Proof idea:

- an inner horn in the strict pullback is a compatible pair of horns in `C` and `D`;
- fill the horn in the non-fibration side using quasicategory structure;
- use the inner-fibration lifting property on the fibration side to make the filler compatible over
  `E`;
- assemble the pair into a simplex in the strict pullback.

This is a good theorem for humans to work through because the proof is standard but requires careful
orientation of horn maps.

### Target C: strict pullback cone API

Once Target B is available, package the strict pullback as a bundled quasicategory with:

- projections;
- strict commutativity of the square;
- a mediating map from a strictly commuting cone;
- strict β-rules;
- strict uniqueness/extensionality.

This part is mostly agent-friendly after the theorem exists.  The companion scaffold already
contains a right-leg version of these wrappers.

### Target D: strict pullbacks as homotopy pullbacks

Under the same fibration hypotheses, prove that the strict pullback represents the homotopy pullback
in the intended ∞-category of quasicategories.

The eventual `HomotopyPullback.Candidate` package should contain more than a strict commuting
square.  Its final shape should be close to the following mathematical data:

1. a quasicategory `P`;
2. projections `p₁ : P → C` and `p₂ : P → D`;
3. a coherent comparison between `p₁ ≫ F` and `p₂ ≫ G`; in the strict-pullback case this comparison
   can be strict equality, but the general SCT field expects natural-isomorphism/coherent data;
4. for every test quasicategory `X`, a map of anima

   ```text
   Map(X,P) → Map(X,C) ×^h_{Map(X,E)} Map(X,D)
   ```

   induced by postcomposition with `p₁` and `p₂` plus the comparison;
5. a proof that this map is an equivalence of anima, i.e. the mapping-anima universal property of a
   homotopy pullback.

Equivalently, one may package a comparison `CatEquiv P H` to a separately constructed
homotopy-pullback object `H`, but the mapping-anima formulation is closer to the SCT fields and to
how `Cat_∞` limits are usually checked.

This is the bridge to the general SCT `pullbackCat` fields.  Without it, strict pullback wrappers
should only be used in fibration-specific fields such as base change.

### Target E: base change of fibrations

For a fibration `p : E → B` and any `q : B' → B`, define the pullback fibration

```text
q^*E := B' ×_B E → B'.
```

Target fields:

- `baseChangeFibration`;
- `baseChangeCartesian`;
- `baseChangeCocartesian`.

Expected steps:

1. model `q^*E` by the strict pullback when `p` satisfies the chosen fibration hypothesis;
2. prove the projection `q^*E → B'` is again a fibration;
3. transport cartesian/cocartesian lift structures across the pullback;
4. package this in the synthetic `Fibration` witness language.

This is a better workshop target than the unrestricted `pullbackCat` block because the hypotheses
make strict simplicial pullbacks semantically justified.

### Target F: directed/lax pullbacks

Chapter 5 uses directed pullbacks whose objects are triples `(a,b, f a → g b)`.

Expected model:

```text
directedPullback(A,B,C,f,g) ≃ strict pullback of
  Fun([1], C) → C × C
against
  A × B → C × C
```

where the first map is `(source,target)` and the second is `(f,g)`.

This depends on:

- functor quasicategory skeleton/upstream replacement;
- arrow-category endpoint maps;
- product and pullback APIs;
- source/target fibration semantics.

This target is likely too large for a first pass, but the design should be recorded while working on
base-change pullbacks.

### Target G: compatibility with object/fiber constructions

Many Chapter 1 constructions are built from pullbacks:

- `fiberCat`;
- `objectSourceFiberCat`;
- `objectHomCat`;
- `natTransSourceFiberCat`;
- `natTransCat`.

If `pullbackCat` is later interpreted by homotopy pullbacks, these derived categories should remain
semantically correct.  A useful checkpoint is the fixed-endpoint hom category:

```text
objectHomCat C x y
```

which should model arrows from `x` to `y` as an endpoint fiber.  This interacts with the §2.6
mapping-anima project, where the fixed-endpoint hom anima is derived from `Map(*, objectHomCat C x
y)`.

## Suggested workshop split

### Project 1: fibration API audit

Goal: choose the fibration notion and locate upstream declarations.

Deliverables:

- a note listing existing mathlib/infinity-cosmos APIs for inner fibrations/categorical fibrations;
- a decision on the local wrapper shape for `InnerFibration`;
- a decision on how it relates to `IsofibrationWitness`.

Good for: human maintainer plus one agent for search/probes.

### Project 2: horn-lifting proof for strict pullback closure

Goal: prove the theorem that a strict pullback of quasicategories along an inner fibration is a
quasicategory.

Deliverables:

- right-leg theorem;
- left-leg theorem, either by symmetry or a separate proof;
- comments explaining the horn orientation.

Good for: human-led formalization.

### Project 3: strict cone wrapper

Goal: package the theorem into a clean bundled API.

Deliverables:

- bundled pullback quasicategory;
- projections;
- strict commutativity;
- lift, β-rules, and uniqueness.

Good for: agent-friendly after Project 2.  The companion Lean scaffold already starts this.

### Project 4: homotopy-pullback comparison

Goal: show the strict pullback under fibration hypotheses has the correct ∞-categorical universal
property.

Deliverables:

- mapping-anima universal property or `CatEquiv` comparison;
- a clear statement of hypotheses;
- a note saying whether this can close any general `pullbackCat` model fields.

Good for: human-interest/upstream work.

### Project 5: base-change fibration package

Goal: build the model package for base-changing fibrations.

Deliverables:

- pullback fibration witness;
- stability of cartesian and cocartesian structures;
- orientation tests for projection names;
- candidate implementations for `baseChangeFibration`, `baseChangeCartesian`, and
  `baseChangeCocartesian`.

Good for: paired human/agent work.

### Project 6: directed pullback design note

Goal: specify the model of `directedPullbackCat` before implementing it.

Deliverables:

- a diagram for the arrow-category endpoint pullback;
- dependency list on functor categories, products, and fibration witnesses;
- names and orientations for `directedPullbackPr1`, `directedPullbackPr2`, and
  `directedPullbackArrow`.

Good for: human design checkpoint.

## Lean scaffold

The file `InternalMath/SCT/IML/Model/FibrationPullbacks.lean` currently contains these placeholders and
wrappers:

```lean
SCTFibrationPullbacksSkeleton.innerHornInclusions
SCTFibrationPullbacksSkeleton.InnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.obj
SCTFibrationPullbacksSkeleton.StrictPullback.quasicategoryOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.quasicategoryOfLeftInnerFibration
  -- already derived from the right-leg theorem by `pullbackSymmetry`
SCTFibrationPullbacksSkeleton.StrictPullback.qcatOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.qcatOfLeftInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.pr1OfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.pr2OfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.commOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.liftOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.lift_pr1_homOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.lift_pr2_homOfRightInnerFibration
SCTFibrationPullbacksSkeleton.StrictPullback.hom_extOfRightInnerFibration
SCTFibrationPullbacksSkeleton.HomotopyPullback.UniversalProperty
SCTFibrationPullbacksSkeleton.HomotopyPullback.Candidate
SCTFibrationPullbacksSkeleton.HomotopyPullback.representedByRightInnerFibration
```

The scaffold gives a right-leg strict cone package and leaves the mathematical closure theorem,
the precise homotopy-pullback universal-property type, and the proof that the strict pullback
satisfies that property as human project markers.

## Informal proof or construction for each current Lean `sorry`

This section tracks every `sorry` currently present in `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`.
If the Lean scaffold changes, update this list in the same commit.  The local `InnerFibration`
wrapper is an `abbrev` for `innerHornInclusions.rlp`, so it is not a `sorry`.  The left-leg
quasicategory theorem is derived from the right-leg theorem by the symmetry isomorphism
`pullback f g ≅ pullback g f`, so it is also not a `sorry`.

### `StrictPullback.quasicategoryOfRightInnerFibration`

Assume `G : D ⟶ E` is an inner fibration and `C`, `D`, and `E` are quasicategories.  Let
`P = C ×_E D` be the strict simplicial-set pullback.  To show `P` is a quasicategory, take an inner
horn `Λ[n,i] ⟶ P`.  Project it to horns `c₀ : Λ[n,i] ⟶ C` and `d₀ : Λ[n,i] ⟶ D`.  Since `C` is a
quasicategory, extend `c₀` to a simplex `c : Δ[n] ⟶ C`.  The pullback condition on the original
horn says `G ∘ d₀ = F ∘ c₀`, while `F ∘ c` is an extension of `F ∘ c₀` to `Δ[n]`.  Thus we have an
inner lifting square against `G` with left map `d₀` and bottom map `F ∘ c`.  Since `G` is an inner
fibration, choose a lift `d : Δ[n] ⟶ D` extending `d₀` and satisfying `G ∘ d = F ∘ c`.  The pair
`(c,d)` therefore defines a simplex `Δ[n] ⟶ P` extending the original horn.  This gives fillers for
all inner horns in `P`, hence `P` is a quasicategory.

### `HomotopyPullback.UniversalProperty`

This is a definition/API target rather than a theorem.  It should be replaced by a structure
expressing the mapping-anima universal property of a homotopy pullback.  Given cone data
`P → C`, `P → D`, and a comparison over `E`, define the comparison map

```text
Map(X,P) → Map(X,C) ×^h_{Map(X,E)} Map(X,D)
```

for every test quasicategory `X`.  The right-hand side should be a homotopy pullback of anima: its
points are pairs of functors `X → C`, `X → D` together with an invertible bicategorical 2-cell
between their composites to `E`, and its higher simplices are the corresponding coherent
equivalences.  The universal-property structure should assert that this comparison is an equivalence
of anima for all `X`.  Once `mapAnima`, `CatEquiv`, and the functor-quasicategory bridge APIs are
available, this can be spelled as fields rather than an abstract placeholder.

### `HomotopyPullback.representedByRightInnerFibration`

The strict cone part is constructed directly: take the candidate object to be
`StrictPullback.qcatOfRightInnerFibration C D E F G hG`, take the projections to be the strict
pullback projections, and use `StrictPullback.commOfRightInnerFibration` for the comparison.  The
remaining mathematical proof is the universal-property field.  For every test quasicategory `X`,
postcomposition induces a map from `Map(X, C ×_E D)` to the homotopy pullback
`Map(X,C) ×^h_{Map(X,E)} Map(X,D)`.  Since `G` is an inner fibration, exponentiation by `X` should
preserve the relevant fibration/isofibration condition, so `Fun(X,D) → Fun(X,E)` is again a
fibration.  Strict pullbacks along such fibrations compute homotopy pullbacks, and the strict
simplicial pullback defining `C ×_E D` is compatible with functor categories, giving
`Fun(X, C ×_E D) ≃ Fun(X,C) ×_{Fun(X,E)} Fun(X,D)`.  Passing to maximal Kan cores gives the desired
equivalence of mapping anima.  This proves that the strict pullback under an inner-fibration
hypothesis represents the homotopy pullback in `Cat_∞`.

## Anti-patterns

Do not use any of these as shortcuts:

- arbitrary strict simplicial-set pullbacks as the general SCT pullback without a homotopy-pullback
  theorem;
- strict equality where the SCT field asks for a `NatIso` comparison;
- `PUnit`/`True` placeholders for fibration witnesses;
- treating all quasicategory maps as fibrations;
- using ordinary categorical pullbacks in the homotopy category as the SCT pullback;
- filling base-change fields before deciding the interpretation of `IsofibrationWitness`.

## Acceptance checks for a serious implementation

A completed implementation should provide:

1. a documented fibration notion and relation to the book's fibration vocabulary;
2. strict-pullback quasicategory closure under explicit fibration hypotheses;
3. a cone API with clear projection orientation;
4. a homotopy-pullback or mapping-anima universal property;
5. base-change stability for the chosen fibration witnesses;
6. a clear statement of which general SCT pullback fields remain open.
