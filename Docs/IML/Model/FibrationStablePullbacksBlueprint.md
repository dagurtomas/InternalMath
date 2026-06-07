# Fibration-stable pullbacks and homotopy pullbacks blueprint

## Project overview

Pullbacks in SCT should behave like homotopy pullbacks of ∞-categories. In a quasicategory model,
a strict pullback has this meaning only when enough fibration hypotheses are present, or when it is
proved to present the derived pullback. This project builds the API that identifies the safe strict
pullbacks and supplies the comparison data needed by the SCT model.

## Project dependencies

- Can start independently for the strict-pullback and fibration-stability API.
- The homotopy-pullback comparison phase depends on
  `Docs/IML/Model/MaximalKanCoreMappingAnimaBlueprint.md`, because the universal property is
  stated using mapping anima.
- The all-cospans `pullbackCat` closure phase also depends on the invertible-arrow and `NatIso`
  bridge from `Docs/IML/Model/IsoRezkModelBlueprint.md`, with Segal-composition support for the
  interval-arrow comparison data.
- The directed/lax pullback phase also uses the functor-quasicategory and arrow-endpoint APIs shared
  with the mapping-anima and Segal-composition projects.

Workshop blueprint for the fibration-stable pullback model scaffold.

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
strict pullback has been shown to represent the derived/homotopy pullback.  The workshop project
starts by building this fibration-stable strict-pullback API.  The full `pullbackCat` plan then
applies the same API to a path-object replacement of the target category, so arbitrary cospans can
be modeled by strict pullbacks along a proven fibration.

Model note: natural transformations are bicategorical 2-cells in mathlib's strict bicategory of
quasicategories. The fibration-pullback scaffold uses strict equality for the special strict cone
where a pullback square commutes on the nose; the homotopy-pullback package should expose coherent
`NatIso` comparison data for general SCT pullbacks.

## Why this is a human workshop project

This project is human-led because it requires semantic choices:

- which notion of fibration should model the book's `IsofibrationWitness`;
- how to relate inner fibrations of simplicial sets to isofibrations of quasicategories;
- whether the model should choose strict pullbacks only under fibrancy hypotheses or use a general
  path-object or fibrant-replacement construction;
- which coherent-isomorphism object should encode the comparison used in arbitrary homotopy
  pullbacks;
- how directed/lax pullbacks in Chapter 5 relate to strict pullbacks and arrow-category pullbacks;
- which parts belong upstream in mathlib/infinity-cosmos.

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

The scaffold defines this local wrapper directly because this mathlib checkout does not appear to
have a named `InnerFibration`. An upstream name can replace it, together with a theorem connecting
it to the book's `IsofibrationWitness` interpretation.

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

Once Target B is available, package the strict pullback as a bundled quasicategory. This is the
ordinary cone picture: the pullback comes with two projections, every other strictly commuting cone
maps into it, and the projections of that mediating map recover the original cone.

The package should include:

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

This is the bridge to the general SCT `pullbackCat` fields.  Until this comparison is available,
strict pullback wrappers should only be used in fibration-specific fields such as base change.

### Target E: arbitrary homotopy pullbacks via a coherent-isomorphism path object

The general SCT field `pullbackCat C D E F G` has no fibration hypothesis on `F` or `G`.  The model
therefore needs a construction that first replaces the ordinary strict pullback problem by a strict
pullback along a proven fibration.

Recommended concrete model:

```text
EqArr(E)        := Fun(IsoWalking, E)
isoEndpoints(E) : EqArr(E) -> E × E
P(F,G)          := (C × D) ×_{E × E} EqArr(E)
```

Here `IsoWalking` is a coherent walking isomorphism, such as the coherent-isomorphism simplicial set
from the incoming invertible-edge API.  An object of `P(F,G)` is a pair of objects `c : C`, `d : D`,
together with a coherent equivalence in `E` from `F c` to `G d`.  This is the usual homotopy
pullback object of ∞-categories.

The decisive theorem is that `isoEndpoints(E)` is the chosen fibration/isofibration.  Then Target B
applies to the strict pullback defining `P(F,G)`, giving a bundled quasicategory for every cospan.
Target D supplies the mapping-anima universal property, either directly for this construction or by
comparing it with any upstream `Cat_∞` homotopy-pullback object.

Alternative route: factor one leg of the cospan, for example

```text
D -> D^fib -> E
```

where the first map is a categorical equivalence over `E` and the second map is the chosen
fibration.  Then define the homotopy pullback as `C ×_E D^fib`.  This can work if an upstream Joyal
model-structure factorization API is easier to use.  The coherent-isomorphism path-object route is
more explicit and gives the comparison data needed by `pullbackComm` and `pullbackLift`.

### Target F: adapter from the homotopy-pullback object to SCT fields

To close the model-structure `pullbackCat` block, package the object `P(F,G)` and its universal
property into the generated SCT fields.

Field plan:

1. `pullbackCat C D E F G` is the bundled quasicategory `P(F,G)`.
2. `pullbackPr1` and `pullbackPr2` are the projections through `C × D`.
3. `pullbackComm` comes from the coherent-isomorphism coordinate of `P(F,G)`, converted to the
   model's `NatIso` representation.
4. `pullbackLift X C D E F G A B θ` is induced by the pair `(A,B)` and the map
   `X -> EqArr(E)` classified by the `NatIso` comparison `θ`.
5. `pullbackBeta1` and `pullbackBeta2` come from the projection β-rules of the strict pullback and
   the product cone, rendered as `NatIso`s.
6. `pullbackEta` comes from the mapping-anima universal property applied to the cone determined by
   a functor `H : X -> P(F,G)`.
7. `pullbackUniq` comes from the same universal property: componentwise `NatIso`s over `C` and `D`
   give a path in the homotopy-pullback mapping anima, hence a `NatIso` between maps into
   `P(F,G)`.

Required bridge APIs:

- a coherent-isomorphism quasicategory and endpoint functors;
- proof that the endpoint map is the chosen fibration/isofibration;
- conversion between invertible bicategorical 2-cells `NatIso X E U V` and maps
  `X -> EqArr(E)` with endpoints `U` and `V`;
- functor-quasicategory compatibility for products, strict pullbacks, and exponentiation by a test
  quasicategory `X`;
- maximal-core/mapping-anima equivalences that turn the universal property into `NatIso`, `CatEquiv`,
  and uniqueness fields in the generated model.

Open design decisions before implementation:

- choose `EqArr(E)` as either a coherent-isomorphism functor category or a full subcategory of the
  arrow category on equivalence arrows;
- choose the exact fibration notion for `isoEndpoints(E)` and relate it to the book's
  `IsofibrationWitness`;
- decide whether the primary universal-property package is a mapping-anima equivalence or a
  `CatEquiv` to an upstream homotopy-pullback object;
- decide which low-level results belong upstream in mathlib or infinity-cosmos.

The blueprint can still specify a complete field path while these API choices are being resolved.
The concrete path-object construction is the recommended route for closing the `pullbackCat`
sorries.

### Target G: base change of fibrations

For a fibration `p : E → B` and any `q : B' → B`, define the pullback fibration

```text
q^*E := B' ×_B E → B'.
```

Informally, this is the family `E` reindexed along the map `q`. The objects over a point of `B'`
are the objects of `E` over its image in `B`, and the fibration structure should transport along
that pullback.

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

### Target H: directed/lax pullbacks

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

### Target I: compatibility with object/fiber constructions

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
- reusable comparison lemmas for strict pullbacks along the chosen fibration class.

Good for: human-interest/upstream work.

### Project 5: coherent-isomorphism path object

Goal: build the all-cospans replacement used by the general `pullbackCat` model field.

Deliverables:

- `EqArr(E)` as either `Fun(IsoWalking,E)` or the equivalent full subcategory of invertible arrows;
- source and target endpoint functors `EqArr(E) -> E × E`;
- proof that the endpoint map is the chosen fibration/isofibration;
- strict-pullback construction
  `(C × D) ×_{E × E} EqArr(E)` as a bundled quasicategory for arbitrary `F` and `G`.

Good for: human-led design with agent support for endpoint bookkeeping.

### Project 6: SCT `pullbackCat` field adapter

Goal: turn the homotopy-pullback construction into implementations for the generated SCT model
fields.

Deliverables:

- candidate implementations for `pullbackCat`, `pullbackPr1`, `pullbackPr2`, and `pullbackComm`;
- conversion from a generated-model `NatIso` comparison to a map into `EqArr(E)`;
- candidate implementation for `pullbackLift`;
- β, η, and uniqueness comparisons derived from the mapping-anima universal property;
- a short dependency note for any remaining fields whose proof uses unfinished `NatIso` or
  mapping-anima adapters.

Good for: paired human/agent work after Projects 4 and 5.

### Project 7: base-change fibration package

Goal: build the model package for base-changing fibrations.

Deliverables:

- pullback fibration witness;
- stability of cartesian and cocartesian structures;
- orientation tests for projection names;
- candidate implementations for `baseChangeFibration`, `baseChangeCartesian`, and
  `baseChangeCocartesian`.

Good for: paired human/agent work.

### Project 8: directed pullback design note

Goal: specify the model of `directedPullbackCat` before implementing it.

Deliverables:

- a diagram for the arrow-category endpoint pullback;
- dependency list on functor categories, products, and fibration witnesses;
- names and orientations for `directedPullbackPr1`, `directedPullbackPr2`, and
  `directedPullbackArrow`.

Good for: human design checkpoint.

## Lean scaffold

The file `InternalMath/SCT/IML/Model/FibrationPullbacks.lean` contains these placeholders and
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

The generated model structure in `InternalMath/SCT/Model.lean` also contains a `pullbackCat` block
of `sorry`s.  Those fields should be closed by the all-cospans path-object plan above; the
strict-pullback scaffold supplies the fibration-stable ingredient.  A useful implementation order
is:

1. prove the strict-pullback closure theorem;
2. define the coherent-isomorphism path object and endpoint fibration;
3. construct `P(F,G) = (C × D) ×_{E × E} EqArr(E)`;
4. prove the mapping-anima universal property for `P(F,G)`;
5. implement `pullbackCat`, projections, comparison, lift, β, η, and uniqueness fields from that
   package.

## Informal proof or construction for each Lean `sorry`

This section tracks every `sorry` present in `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`.
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
main mathematical proof is the universal-property field. For every test quasicategory `X`,
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

- arbitrary strict simplicial-set pullbacks as the general SCT pullback without a path-object or
  homotopy-pullback theorem;
- strict equality where the SCT field asks for a `NatIso` comparison;
- `PUnit`/`True` placeholders for fibration witnesses;
- treating all quasicategory maps as fibrations;
- using ordinary categorical pullbacks in the homotopy category as the SCT pullback;
- filling base-change fields before deciding the interpretation of `IsofibrationWitness`.

## Expected implementation

A completed implementation should provide:

1. a documented fibration notion and relation to the book's fibration vocabulary;
2. strict-pullback quasicategory closure under explicit fibration hypotheses;
3. a cone API with clear projection orientation;
4. a homotopy-pullback or mapping-anima universal property;
5. a coherent-isomorphism path-object construction for arbitrary cospans;
6. generated-model implementations for the `pullbackCat` block in `InternalMath/SCT/Model.lean`;
7. base-change stability for the chosen fibration witnesses;
8. a clear statement of any remaining pullback-dependent SCT fields that need later adapters.
