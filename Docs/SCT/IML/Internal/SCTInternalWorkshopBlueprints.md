# SCT internal workshop project blueprints

Status: refreshed after the SCT IML reorganization and lint check, 2026-06-04.

Scope: this note triages `sorry`-admitted internal declarations in the staged modules under
`InternalMath/SCT/Spec/` and evaluates whether larger internal developments such as Yoneda, limits,
and colimits are ready for workshop work. It is the internal-theory analogue of
`Docs/SCT/IML/Model/SCTModelFormalizationBlueprints.md`. The old spec-split plan is historical:
`InternalMath/SCT/Spec.lean` is the stable aggregate import and the real targets are the staged
chapter modules. The Lean specification has not moved under `InternalMath/SCT/IML`; only these
workshop blueprints live under `Docs/SCT/IML/Internal/`.

This is about working inside SCT itself. It is separate from the external quasicategory model
scaffolds in `InternalMath/SCT/IML/Model/MappingAnima.lean`,
`InternalMath/SCT/IML/Model/FibrationPullbacks.lean`, and
`InternalMath/SCT/IML/Model/Localization.lean`.

## Current baseline

The diagnostic command

```lean
import InternalMath.SCT.Spec

#lint_type_theory_sorries SCT
#check_model_obligations SCT
```

currently reports 64 admitted internal declarations through the aggregate `Spec.lean` import. This
count was rechecked on 2026-06-04 after the IML reorganization. The model-obligation check still
reports the generic LF-model backend check; the issue here is internal theorem/definition debt, not
temporary admitted-definition fields in the generated model interface.

Older local planning notes may have stale counts. This public blueprint uses the current
64-declaration lint output.

## Classification labels

Use these labels when selecting workshop projects.

- **Foundation blocker**: closes prerequisites used by many downstream theorems.
- **High-value theorem**: directly proves a book theorem or important internal adapter.
- **Design project**: the current statement is too coarse; first decide the source-faithful API.
- **Agent-after-design**: good for implementation once a human fixes the statement and proof plan.
- **Downstream/VH**: valuable, but depends on several earlier workshop projects.
- **Model-adjacent**: best coordinated with the quasicategory model scaffolds.

## Executive summary

Best near-term human projects:

1. **Full subcategory and subcategory witness infrastructure.**
   Detailed blueprint: `Docs/SCT/IML/Internal/SubcategoryFullSubcategoryInternalBlueprint.md`.
   This unlocks many Chapter 3, Rezk/Iso, localization, and Chapter 6 statements.
2. **Strong-surjectivity object extraction.**
   Detailed blueprint: `Docs/SCT/IML/Internal/StrongSurjectivityInternalBlueprint.md`.
   A focused Chapter 6 target with only two current admissions and a clear proof idea from the
   definition of strong surjectivity.
3. **Core/mapping-anima internal adapters.**
   These should follow the maximal-Kan-core workshop project and would simplify many groupoid/core
   proofs.
4. **Over categories and slices as a source-faithful API.**
   This is the best prerequisite project for later limits, colimits, and Yoneda.
5. **Localization/geometric-realization internal consequences.**
   Good after the localization scaffold has a settled universal-property shape.

Projects to avoid as first workshop targets:

- the full Fundamental Theorem of category theory;
- Yoneda itself;
- general limits and colimits as theorem-proving projects;
- straightening/unstraightening and universe regularity.

Those topics are feasible as **blueprint/API-design projects**, but not as direct sorry-closing
projects yet.

## Current admitted declarations by cluster

### Chapter 2: cores, mapping anima, and groupoids

Current admissions:

- `mapAnimaCoreEquiv`;
- `funCatTargetGroupoid`;
- `intervalCoreEndpointEquiv`;
- `coreProductEquiv`;
- `corePullbackEquiv`;
- `simplex2CoreEndpointEquiv`;
- `coprodGroupoid`;
- `pullbackGroupoid`;
- `initialGroupoid`.

Classification: **Model-adjacent foundation blockers**.

These are high value, but most depend on the same semantic package as the mapping-anima scaffold:
`Map(C,D)` should be `Fun(C,D)^≃`, groupoids should be anima/Kan objects, and cores should have a
usable universal property.  Do not try to prove these in isolation from the maximal-core project.

Best workshop shape:

1. connect `mapAnima` to `coreCat (funCat C D)`;
2. prove functor categories into groupoids are groupoids;
3. prove finite closure of groupoids/cores;
4. compute the cores of `[1]` and `[2]`.

Likely order:

```text
mapAnimaCoreEquiv
funCatTargetGroupoid
initialGroupoid / coprodGroupoid / pullbackGroupoid
coreProductEquiv / corePullbackEquiv
intervalCoreEndpointEquiv / simplex2CoreEndpointEquiv
```

### Chapter 3: subcategories, full subcategories, and all morphisms

Current admissions:

- `idSubcategoryWitness`;
- `initialSubcategoryWitness`;
- `subcategoryWitnessEmbedding`;
- `all_morphisms_contains_identities`;
- `all_morphisms_closed`;
- `subcategoryInclWitness`;
- `fullSubcategoryCoreEquiv`;
- `fullSubcategoryAllObjectsEquiv`;
- `fullSubcategoryInclLands`;
- `landsInObjectCollectionPreservesFull`.

Classification: **Foundation blocker**, with some **Agent-after-design** components.

This is probably the best high-value internal workshop target.  The key issue is that the current
subcategory/full-subcategory interface stores enough data to use the constructions, but not enough
of the book's projection data to prove all expected consequences cleanly.

Recommended split:

1. Revisit `SubcategoryWitness` and decide whether it should be an explicit structure matching the
   book's criterion rather than an opaque witness sort.
2. Make `subcategoryInclWitness` a projection of the subcategory package if the package really
   contains the book universal property.
3. Prove `subcategoryWitnessEmbedding` from the book's subcategory criterion.
4. Define or characterize `allMorphisms` as the total morphism subobject, so identity and
   composition closure are by construction.
5. Prove the full-subcategory landing and preservation lemmas.
6. Prove the core/full-subcategory comparison.

High-value outcomes:

- better `Iso(C)` and Rezk adapters;
- cleaner localization and inverting-functor categories;
- prerequisites for Chapter 6 full-subcategory equivalence theorems;
- a healthier internal foundation for future Yoneda/presheaf work.

### Chapter 3: inverting functors, localization, and realization

Current admissions:

- `invertingFunctorTargetGroupoidEquiv`;
- `localizationPushoutSquare`;
- `geometric_realization_is_anima`.

Classification: **High-value theorem**, **Model-adjacent**, not first.

These belong with the detailed localization scaffold.  The correct proof of
`geometric_realization_is_anima` should say that localization at all morphisms produces a groupoid,
then use the groupoid/anima comparison.  The pushout square should be derived from the localization
universal property and the inverting-functor category, not postulated independently.

Prerequisites:

- `Inverts` phrased through invertible arrows/equivalence edges;
- `Fun_W(C,D)` as a real full subcategory;
- `invertingFunctorTargetGroupoidEquiv`, from the theorem that all arrows in a groupoid target are
  invertible;
- a mapping-anima or functor-category equivalence universal property for localization.

This is a good workshop project after the subcategory and localization-interface projects have
settled their APIs.

### Chapter 3/4: over categories, dependent products, relative joins, and contexts

Current admissions:

- `overCat`;
- `overPullbackFunctor`;
- `dependentProductFunctor`;
- `dependentProductBeckChevalley`;
- `relativeJoinCat`;
- `relativeJoinInl`;
- `relativeJoinInr`;
- `contextCategoryCat`;
- `contextCategoryObject`;
- `overFunctorToContext`;
- `contextOverCorrespondence`.

Classification: **Design project**, high value.

This is the best internal project if the goal is to prepare for limits, colimits, Yoneda, and
category theory in context.  The immediate proof burden is too large, but the API design is ready
for a workshop.

Core design choices:

1. Define `overCat B` as a slice/fiber of a functor category over `B`.
2. Define pullback/reindexing `overCat B → overCat A` by strict pullback or by the SCT pullback
   universal property.
3. Decide whether dependent products should be represented as right adjoints to pullback functors in
   over-categories, or only through the book's exponentiable-functor package.
4. Define relative joins from joins plus dependent products over a base.
5. Relate `ContextCat Γ` to `overCat Γ` via `contextOverCorrespondence`.

Good workshop deliverable: a detailed blueprint and small Lean skeleton, analogous to the mapping
anima/fibration/localization scaffolds, before trying to close these admissions.

### Chapter 6: fully faithful, conservative, and strongly surjective functors

Current admissions:

- `fullyFaithfulHomEquiv`;
- `fullyFaithfulConservative`;
- `conservativeReflectsIso`;
- `stronglySurjectivePreimage`;
- `stronglySurjectiveBeta`;
- `conservativeOfRetract`;
- `fundamental_theorem_equiv`;
- `equivalenceFullyFaithful`;
- `equivalenceStronglySurjective`;
- `fullSubcategoryEquivOfStronglySurjective`;
- `cocartesianFunctorFiberwiseEquiv`;
- `funCatPostcompFullyFaithful`.

Classification: mixed.  The cluster is high value, but the full theorem is downstream.

Recommended near-term target: **strong-surjectivity object extraction**.

The definition of `StronglySurjective C D F` already gives a section

```text
s : coreCat D → coreCat C
```

and a comparison `s ≫ F^≃ ≅ id`.  Given an object `y : * → D`, use the core universal property for
maps from the groupoid `*` to lift `y` to `coreCat D`, apply `s`, and then include back into `C` to
obtain the chosen preimage.  The beta comparison should be obtained by composing the strong
surjectivity beta with the core-inclusion beta.  This project has only two admissions:

```text
stronglySurjectivePreimage
stronglySurjectiveBeta
```

and is a good human+agent target.

Recommended later order:

1. `stronglySurjectivePreimage`, `stronglySurjectiveBeta`;
2. `fullyFaithfulHomEquiv`, from the endpoint-pullback definition;
3. `conservativeReflectsIso`, by unpacking the core-pullback criterion;
4. `fullyFaithfulConservative`;
5. `equivalenceFullyFaithful`, `equivalenceStronglySurjective`;
6. `fundamental_theorem_equiv`;
7. `fullSubcategoryEquivOfStronglySurjective` and `funCatPostcompFullyFaithful`;
8. `cocartesianFunctorFiberwiseEquiv` after fibration transport is stable.

The Fundamental Theorem should not be the first project.  It depends on objectwise natural
isomorphism, full faithfulness on hom categories, strong-surjectivity extraction, conservativity,
and the current `CatEquiv` calculus.

### Chapter 7: cocartesian functor categories and straightening over `[1]`

Current admissions:

- `isCocartesianFunctorCat`;
- `cocartesianFunctorCatSubcategory`;
- `straighteningFunctor`;
- `straighteningFunctorCocartesian`.

Classification: **Downstream/VH**.

These are important, but they should wait for:

- a real non-full subcategory construction or a subcategory API matching the book;
- stable fibration and cocartesian-functor witnesses;
- the over-category/context correspondence;
- the directed-univalence API.

A useful near-term workshop project would be a design note for the category of cocartesian functors,
not a direct proof attempt.

### Chapter 7: internal category universe and universe closure

Current admissions:

- `catInternalInitial`;
- `catInternalProduct`;
- `catInternalCoproduct`;
- `catInternalPullback`;
- `catInternalFunctorCategory`;
- `geometricRealizationSmall`;
- `fiberwiseLocalizationTotal`;
- `fiberwiseLocalizationProjection`;
- `fiberwiseLocalizationFibration`;
- `fiberwiseLocalizationCocartesian`;
- `cocartesianFibrationsOverCat`;
- `straighteningUnstraighteningEquiv`;
- `universalComposablePairCat`;
- `universalComposablePairProjection`;
- `regularOfConstructiveRegular`.

Classification: **Downstream/VH**.

These are not good first workshop targets.  They depend on directed univalence, universe closure,
straightening/unstraightening, localization, and the internal `Cat` object.  They are suitable for a
long-term design seminar after the Chapter 3 and Chapter 6 foundations are healthier.

## Recommended workshop project menu

### Good first human-led projects

1. **Subcategory witness and full-subcategory consequences.**
   Start with `subcategoryInclWitness`, `subcategoryWitnessEmbedding`, `fullSubcategoryInclLands`,
   and `landsInObjectCollectionPreservesFull`.
2. **Strong-surjectivity extraction.**
   Close `stronglySurjectivePreimage` and `stronglySurjectiveBeta`.
3. **Over-category API blueprint.**
   Design `overCat`, reindexing, dependent products, and context-over correspondence.
4. **All-morphisms collection.**
   Make `allMorphisms` behave like the total morphism subobject and prove identity/composition
   closure.

### Good paired projects

1. **Full-subcategory core comparison.**
   Prove `fullSubcategoryCoreEquiv` and `fullSubcategoryAllObjectsEquiv` after landing lemmas.
2. **Fully faithful on hom categories.**
   Prove `fullyFaithfulHomEquiv` from the endpoint-pullback definition.
3. **Core finite-closure consequences.**
   Work on `initialGroupoid`, `coprodGroupoid`, `pullbackGroupoid`, `coreProductEquiv`, and
   `corePullbackEquiv` after the maximal-core API stabilizes.
4. **Localization internal consequences.**
   Work on `invertingFunctorTargetGroupoidEquiv`, `localizationPushoutSquare`, and
   `geometric_realization_is_anima` after the localization scaffold stabilizes.

### Good agent-after-design projects

1. Endpoint and object bookkeeping in `stronglySurjectivePreimage`/`stronglySurjectiveBeta`.
2. Projection lemmas from a redesigned `SubcategoryWitness`.
3. Naturality and whiskering chains in Chapter 6 once the main proof idea is fixed.
4. Adapters from future over-category and localization packages to the existing SCT names.

### Poor first projects

1. `fundamental_theorem_equiv` directly.
2. Yoneda lemma directly.
3. General `limitFunctor`/`colimitFunctor` theory directly.
4. Straightening/unstraightening directly.
5. Universe regularity and constructive regularity directly.

## Feasibility: Yoneda lemma

Yoneda is not ready as a direct formalization target.

Reasons:

- `Spec.lean` currently has no Yoneda, presheaf, representable, or opposite-category API.
- A presheaf category should be something like `Fun(Cᵒᵖ, Anima)` or `Fun(Cᵒᵖ, Grpd)`.  The file
  does not yet have `opCat`, a category of anima as an internal target, or a settled internal
  category of groupoids suitable for presheaves.
- The mapping-anima/core story is still under construction.  Yoneda should use mapping objects
  coherently, not bare strict hom sets.
- Natural transformations and objectwise criteria still rely on primitive data; the Chapter 6
  objectwise/functor-category theory is not yet robust enough for a clean Yoneda proof.
- Slices and over-categories exist only partially.  Many synthetic proofs of Yoneda use slice or
  comma-category reasoning.

Feasible workshop version:

```text
Yoneda prerequisites and API blueprint
```

Deliverables:

1. decide on `opCat` and variance conventions;
2. define a presheaf category target, probably via a groupoid/anima universe;
3. define representables using `mapAnima` or fixed-endpoint hom anima;
4. state the Yoneda evaluation equivalence;
5. list dependencies on the Fundamental Theorem, full faithfulness, and objectwise natural
   isomorphisms.

A small Lean skeleton would be useful only after the over-category/context and groupoid-universe
APIs are clearer.  It should not be sold as a proof project yet.

## Feasibility: limits and colimits

The file already has a thin Chapter 5 vocabulary layer:

```text
Diagram J C := Functor J C
coneCat J C D
coconeCat J C D
LimitCone J C D
ColimitCocone J C D
HasLimitsOfShape J C
HasColimitsOfShape J C
limitFunctor J C h
colimitFunctor J C h
```

This is enough to state that a category admits limits or colimits of a shape, but it is too coarse
for serious internal theorem proving.  It lacks explicit cone/cocone universal properties, constant
diagram functors, β/η rules, uniqueness clauses, and adjunction data.

Feasible now:

- finite examples using the existing terminal/product/pullback and initial/coproduct primitives;
- a blueprint for source-faithful cone and cocone categories;
- a design note relating limits to terminal objects in cone categories and colimits to initial
  objects in cocone categories;
- adapters showing that existing finite limits/colimits are special cases of a future general API.

Not feasible yet as direct proof projects:

- a general theorem that products/pullbacks are limits of their shapes;
- general adjunctions between constant diagrams and limit/colimit functors;
- cofinality;
- filtered colimits of anima.

Prerequisites for serious limits/colimits work:

1. source-faithful `overCat`, slices, and reindexing;
2. cone/cocone categories defined through joins/slices or functor-category pullbacks;
3. terminal/initial object witness API with enough projections;
4. functor-category and natural-isomorphism calculus;
5. for colimits, duality/opposite categories or separately duplicated cocone constructions;
6. for later cofinality/Yoneda interactions, mapping-anima universal properties.

Recommended workshop target:

```text
General limits and colimits API blueprint
```

rather than attempting to close `limitFunctor` or `colimitFunctor`, which are current axiom data.

## Dependency map for ambitious theorems

```text
Subcategory/full-subcategory API
  → Iso(C), invertible arrows, allMorphisms
  → inverting functor categories
  → localization and geometric realization

Mapping anima and maximal cores
  → core finite closure
  → groupoid closure
  → object/morphism collections
  → presheaf/Yoneda prerequisites

Over categories and slices
  → context-over correspondence
  → dependent products and relative joins
  → cone/cocone categories
  → limits and colimits
  → Yoneda/cofinality later

Strong-surjectivity extraction + fully faithful hom equivalence
  → conservativity results
  → Fundamental Theorem
  → equivalences preserve/reflect many structures
  → full-subcategory equivalence theorems

Fibration and universe APIs
  → cocartesian functor categories
  → straightening/unstraightening
  → internal Cat and groupoid universes
  → Yoneda/presheaves at universe level
```

## Suggested next document blueprints

If workshop participants want more detailed project notes, write these next:

1. `Docs/SCT/IML/Internal/SubcategoryFullSubcategoryInternalBlueprint.md` (written).
2. `Docs/SCT/IML/Internal/StrongSurjectivityInternalBlueprint.md` (written).
3. `Docs/SCT/IML/Internal/OverCategoriesAndSlicesBlueprint.md`.
4. `Docs/SCT/IML/Internal/LimitsColimitsInternalBlueprint.md`.
5. `Docs/SCT/IML/Internal/YonedaPrerequisitesBlueprint.md`.

The first two are the most realistic for actually closing current internal `sorry`s.
