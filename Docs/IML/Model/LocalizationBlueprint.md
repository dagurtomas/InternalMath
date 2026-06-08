# Inverting-functor categories and localization blueprint

## Project overview

Localization freely turns a chosen collection of arrows into equivalences. For a category `C` and a
morphism collection `W`, the localized category `C[W⁻¹]` should be universal for functors out of
`C` that send every arrow in `W` to an equivalence. This project builds that quasicategorical
universal property and connects it to the SCT localization fields.

## Project dependencies

- The upstream/API audit and universal-property design can start independently.
- Completing the inverting-functor and localization packages depends on
  `Docs/IML/Model/FunctorQuasicategoryBridgeBlueprint.md` for the bridge from bicategorical
  2-cells to edges of functor quasicategories, and on
  `Docs/IML/Model/MaximalKanCoreMappingAnimaBlueprint.md` for mapping anima, maximal cores,
  equivalence edges, and the meaning of `Map_W(C,D)`.
- The project uses the invertible-arrow object collection from
  `Docs/IML/Model/IsoRezkModelBlueprint.md`, or at least the same equivalence-edge API, to express
  that a functor sends the arrows of `W` to equivalences.
- The geometric-realization/groupoid-completion phase should wait until the localization universal
  property and the groupoid-core adapters are in place.

Workshop blueprint for the localization model scaffold.

Scope: this note expands the project around functors that invert a morphism collection and
quasicategorical localization in `InternalMath/SCT/Model.lean`. The companion Lean scaffold is
`InternalMath/SCT/IML/Model/Localization.lean`.

## Short version

The intended model interpretation is:

```text
Fun_W(C,D)  := full subcategory of Fun(C,D) spanned by functors inverting W
C[W⁻¹]      := quasicategorical localization of C at W
```

The universal property should be quasicategorical:

```text
Fun(C[W⁻¹], D) ≃ Fun_W(C,D)
```

or, after passing to maximal Kan cores,

```text
Map(C[W⁻¹], D) ≃ Map_W(C,D).
```

Here `W` is a morphism collection in `C`, represented semantically as a subobject of the mapping
anima of arrows in `C`.  A functor inverts `W` when every arrow selected by `W` is sent to an
equivalence edge.

This is the generic localization interface needed for future derived ∞-categories such as
`Ch(A)[Qis⁻¹]`.  It does not by itself construct chain complexes, quasi-isomorphisms, stable
∞-categories, or triangulated homotopy categories.

## Design choices

This project requires several semantic choices:

- how to represent morphism collections: as subobjects of `Map([1],C)`, as subcomplexes of the
  arrow quasicategory, or via a future upstream subcategory API;
- how to define the inverting-functor object collection inside `Fun(C,D)`;
- which notion of equivalence of quasicategories should state the universal property;
- how much of the Dwyer--Kan localization theorem should be imported from upstream and how much
  should be wrapped locally;
- how the SCT descender/β/uniqueness fields should be extracted from a quasicategorical universal
  equivalence.

The proof of existence and the universal property are part of the main mathematical content.

## Existing SCT declarations involved

Primitive or model fields:

- `InvertsMorphismCollection`;
- `localizationCat`;
- `localizationFunctor`;
- `localizationInverts`;
- `invertingFunctorObjectPackage`;
- `localizationUniversalPackage`.

Derived declarations already in `Spec.lean`:

- `invertingFunctorObjects`;
- `invertingFunctorCat`;
- `invertingFunctorIncl`;
- `invertingFunctorSubcategoryWitness`;
- `localizationDesc`;
- `localizationDescBeta`;
- `localizationDescUniq`;
- `localizationUniversalEquiv`;
- `geometricRealization C := localizationCat C (allMorphisms C)`;
- `geometricRealizationFunctor` and the groupoid-completion comparison fields.

The model should make these agree with the quasicategorical semantics instead of treating
localization as ordinary localization of homotopy categories.

## Mathematical targets

### Target A: functor quasicategories

Use or import a quasicategory of functors:

```lean
Fun(C,D)
```

For simplicial sets this should be the simplicial internal hom `D^C`, bundled with the theorem that
it is a quasicategory when `C` and `D` are quasicategories.  This target overlaps with the existing
functor-quasicategory/internal-hom skeleton in `InternalMath/SCT/Model.lean`.  The model interprets
natural transformations as bicategory 2-cells, so localization also needs the bridge from those
2-cells to the internal-hom functor quasicategory.

Needed operations:

1. vertices of `Fun(C,D)` correspond to maps `C → D`;
2. composition/precomposition/postcomposition are functors between functor quasicategories;
3. bicategory 2-cells are connected to edges or homotopy classes of edges in `Fun(C,D)`;
4. equivalence edges in `Fun(C,D)` correspond to invertible 2-cells;
5. maximal cores of functor quasicategories give mapping anima.

### Target B: morphism collections

For a quasicategory `C`, a morphism collection should be a subobject of the mapping anima of arrows:

```text
W ↪ Map([1], C).
```

This matches the SCT encoding where `MorphismCollection C` is an anima subobject of
`morphismAnima C`.  Semantically, points of `W` are arrows of `C` and higher simplices are coherent
families of arrows.

Expected model-side ingredients:

1. the walking-arrow quasicategory `Δ[1]` or its nerve model;
2. `Map([1], C)` as the maximal core of `Fun([1],C)`;
3. a subobject/embedding representation for anima;
4. evaluation maps extracting source, target, and underlying interval-shaped arrow.

### Target C: functors that invert a morphism collection

Given `W` in `C` and `F : C → D`, define:

```text
Inverts(W,F)
```

by requiring that every selected arrow of `C` is sent to an equivalence in `D`.

A useful semantic description is the factorization condition:

```text
W → Map([1], C) → Map([1], D)
```

lands in the subobject of invertible arrows of `D`.  The second map is induced by postcomposition
with `F` on arrow objects.  The invertible-arrow object should come from the maximal core or
equivalence-edge API, not from a strict equality or ordinary isomorphism placeholder.

### Target D: inverting-functor category

Define `Fun_W(C,D)` as the full sub-quasicategory of `Fun(C,D)` on vertices satisfying
`Inverts(W,-)`. This category keeps exactly the functors that send the selected arrows to
equivalences, while leaving natural transformations between such functors unchanged.

Expected API shape:

```lean
invertingFunctorCat (C D : QCat) (W : MorphismCollection C) : QCat
invertingFunctorIncl : invertingFunctorCat C D W ⟶ Fun(C,D)
```

The object collection should be equivalent to `Inverts(W,F)` for every vertex `F : C → D`.  The
inclusion should be a full subcategory.  Natural transformations between inverting functors are just
natural transformations in `Fun(C,D)`, with no extra condition on edges.

### Target E: localization candidate

A localization candidate is the data that presents `C` after the arrows in `W` have been made
invertible. The category `L` is the result, `loc : C → L` is the comparison functor, and the
universal property says that maps out of `L` are the same as maps out of `C` that already invert
`W`.

The package consists of:

1. a quasicategory `L`;
2. a functor `loc : C → L`;
3. evidence that `loc` inverts `W`;
4. a quasicategorical universal property.

This should feed the SCT fields:

```text
localizationCat C W        := L
localizationFunctor C W    := loc
localizationInverts C W    := evidence for loc
```

The first three fields are not enough.  They must be accompanied by the universal property to be a
localization.

### Target F: universal property

The strongest useful statement is that, for every quasicategory `D`, precomposition with `loc`
induces an equivalence:

```text
Fun(L,D) ≃ Fun_W(C,D).
```

The mapping-anima version is:

```text
Map(L,D) ≃ Map_W(C,D).
```

Here `Map_W(C,D)` is the maximal core of `Fun_W(C,D)`.  This statement should provide the SCT
`localizationUniversalPackage`: a universal equivalence, descents of inverting functors, β
comparisons, and uniqueness comparisons.  The descender sends an inverting functor `F : C → D` to a
functor `K : L → D` with a natural isomorphism `loc ≫ K ≅ F`, unique up to natural isomorphism.

### Target G: existence theorem

Import or formalize the quasicategorical/Dwyer--Kan localization theorem:

```text
For every quasicategory C and suitable morphism collection W, C[W⁻¹] exists and satisfies Target F.
```

Possible implementations:

1. wrap an upstream localization construction;
2. use a marked simplicial-set or relative-category model and compare to quasicategories;
3. construct a simplicial localization and take its coherent nerve;
4. use a known theorem from the Joyal model structure if it becomes available in mathlib.

The chosen route should expose a quasicategory and a functor out of `C`. A construction only at the
homotopy-category level loses the higher mapping data needed by SCT.

### Target H: geometric realization/groupoid completion

The SCT geometric realization field is localization at all morphisms:

```text
∥C∥ := C[Mor(C)⁻¹].
```

After localization is implemented, prove that `∥C∥` is a groupoid/Kan complex.  Semantically this is
groupoid completion.  It should be a theorem from localization plus the fact that every morphism has
been inverted, rather than a separate primitive groupoid witness.

## Suggested workshop split

### Project 1: upstream/API audit

Goal: identify existing or incoming APIs for functor quasicategories, full subcategories,
equivalence edges, and localization.

Deliverables:

- list of mathlib/infinity-cosmos declarations to wrap;
- decision on whether the local skeleton should keep `MorphismCollection` abstract or use a concrete
  subobject representation;
- replacement plan for the placeholders in `InternalMath/SCT/IML/Model/Localization.lean`.

### Project 2: morphism collections as subobjects

Goal: model `MorphismCollection C` as a subobject of `Map([1],C)`.

Deliverables:

- a bundled subobject or subcomplex representation;
- source/target/arrow evaluation maps;
- comparison with the internal SCT `morphismCollectionCat`, `morphismCollectionIncl`, and
  `morphismCollectionArrowObject` declarations.

### Project 3: inversion predicate

Goal: define `Inverts W F` using the invertible-arrow object in the target.

Deliverables:

- arrow-action functor induced by `F`;
- factorization of `W` through invertible arrows in `D`;
- stability under postcomposition by arbitrary functors;
- proof that functors into a groupoid invert every morphism collection.

### Project 4: inverting-functor full subcategory

Goal: build `Fun_W(C,D)` as a full subcategory of `Fun(C,D)`.

Deliverables:

- object collection of inverting functors;
- inclusion into `Fun(C,D)`;
- membership iff `Inverts W F`;
- full-subcategory witness;
- maximal core `Map_W(C,D)`.

### Project 5: universal property package

Goal: design the exact Lean shape of localization's universal property.

Deliverables:

- comparison functor `Fun(L,D) → Fun_W(C,D)` by precomposition;
- equivalence or mapping-anima equivalence field;
- projections yielding `localizationDesc`, `localizationDescBeta`, `localizationDescUniq`;
- naturality in `D` if needed by later SCT developments.

### Project 6: localization existence

Goal: import or construct `C[W⁻¹]`.

Deliverables:

- localized quasicategory;
- localization functor;
- proof it inverts `W`;
- universal property;
- adapter closing the relevant SCT model fields.

### Project 7: downstream applications

Goal: connect localization to groupoid completion and later derived ∞-categories.

Deliverables:

- `∥C∥ = C[Mor(C)⁻¹]` as a Kan complex;
- compatibility with `mapAnima` and `coreCat`;
- roadmap for derived ∞-categories `Ch(A)[Qis⁻¹]` once chain complexes and quasi-isomorphisms are
  available.

## Companion Lean scaffold

The companion file `InternalMath/SCT/IML/Model/Localization.lean` defines the namespace
`SCTLocalizationSkeleton` with these declarations:

```lean
SCTLocalizationSkeleton.FunctorQuasicategory.obj
SCTLocalizationSkeleton.MorphismCollection
SCTLocalizationSkeleton.Inverts
SCTLocalizationSkeleton.InvertingFunctorCategory.obj
SCTLocalizationSkeleton.InvertingFunctorCategory.incl
SCTLocalizationSkeleton.Localization.precomp
SCTLocalizationSkeleton.Localization.UniversalProperty
SCTLocalizationSkeleton.Localization.Candidate
SCTLocalizationSkeleton.Localization.candidate
SCTLocalizationSkeleton.Localization.cat
SCTLocalizationSkeleton.Localization.functor
SCTLocalizationSkeleton.Localization.inverts
SCTLocalizationSkeleton.Localization.universal
```

The scaffold stops before filling `sctModel` fields. It names the mathematical seams and records
the existence theorem and API choices as project milestones.

## Informal proof or construction for each Lean `sorry`

This section tracks every `sorry` present in `InternalMath/SCT/IML/Model/Localization.lean`.  If the
Lean scaffold changes, update this list in the same commit.

### `FunctorQuasicategory.obj`

Use the simplicial internal hom construction.  For quasicategories `C` and `D`, define the
underlying simplicial set of `Fun(C,D)` to be `D.obj ^ C.obj`, or the corresponding mathlib
internal-hom notation.  Vertices are simplicial maps `C.obj → D.obj`, so they agree with morphisms
`C ⟶ D` in the bundled quasicategory category.  The missing theorem is that the internal hom is a
quasicategory when the codomain is a quasicategory, in the setting needed by the project.  Once that
theorem is imported, bundle the internal hom as an `SSet.QCat`.

### `MorphismCollection`

Replace the abstract type by a concrete subobject representation.  The book's semantic target is a
subobject of the morphism anima, so model `W` as a Kan complex or anima equipped with an embedding

```text
W ↪ Map([1], C).
```

Here `Map([1],C)` is the maximal core of `Fun([1],C)`.  Points of `W` are arrows of `C`; higher
simplices encode coherent families of arrows.  The embedding property supplies the subobject
behavior needed by full subcategories and localization.

### `Inverts`

Given `W ↪ Map([1],C)` and `F : C → D`, postcomposition with `F` induces

```text
Map([1],C) → Map([1],D).
```

Restrict this map along `W`.  The functor `F` inverts `W` exactly when the resulting map factors
through the subobject of invertible arrows in `D`, equivalently through `Iso(D)` or the maximal
core/invertible-arrow object inside `Fun([1],D)`.  The proof obligations are preservation of
selected arrows by postcomposition and compatibility between the invertible-arrow object and the
equivalence-edge API.

### `InvertingFunctorCategory.obj`

Construct the object collection in `Fun(C,D)` whose vertices are functors `F : C → D` satisfying
`Inverts W F`.  Then apply the quasicategorical full-subcategory construction to obtain a
quasicategory.  Higher simplices are the same higher natural transformations as in `Fun(C,D)`
whenever all vertices satisfy the inverting condition.  The construction should also provide the
membership equivalence between vertices of this full subcategory and inversion evidence.

### `InvertingFunctorCategory.incl`

Use the inclusion supplied by the full-subcategory construction in the previous item.  On vertices
it forgets the proof that a functor inverts `W`; on higher simplices it is the ambient inclusion
into `Fun(C,D)`.  The formal proof should show that this inclusion is full and that its image is
exactly the object collection of inverting functors.

### `Localization.precomp`

For a localization candidate `loc : C → L` and a target `D`, define precomposition by

```text
K ↦ loc ≫ K
```

for `K : L → D`.  This gives a functor `Fun(L,D) → Fun(C,D)`.  To land in `Fun_W(C,D)`, prove that
`loc ≫ K` inverts `W`: `loc` sends arrows of `W` to equivalences in `L`, and every functor
`K : L → D` preserves equivalence edges.  The full-subcategory lift into `Fun_W(C,D)` then gives the
required comparison functor.

### `Localization.UniversalProperty`

Replace this placeholder by a structure expressing the localization universal property.  For every
quasicategory `D`, the comparison functor from `Localization.precomp` should be an equivalence

```text
Fun(L,D) ≃ Fun_W(C,D).
```

Equivalently, after applying maximal cores, it should induce an equivalence of anima

```text
Map(L,D) ≃ Map_W(C,D).
```

The structure should expose enough data to build the SCT package: for every inverting functor
`F : C → D`, a descended functor `K : L → D`, a natural isomorphism `loc ≫ K ≅ F`, and uniqueness of
`K` up to natural isomorphism.  It should also include or imply the equivalence
`Fun(L,D) ≃ Fun_W(C,D)` used by `localizationUniversalEquiv`.

### `Localization.candidate`

Use a genuine quasicategorical localization theorem.  Starting from `C` and `W`, construct or import
a quasicategory `C[W⁻¹]`, a functor `loc : C → C[W⁻¹]`, proof that `loc` inverts `W`, and proof of
the universal property above.  Acceptable routes include wrapping an upstream Dwyer--Kan
localization construction, using marked simplicial sets or relative categories and taking a coherent
nerve, or importing a theorem from the Joyal model structure.  The result must not be the ordinary
localization of `Ho(C)`; it must retain the higher mapping-anima information.

## Anti-patterns

Do not use any of these as shortcuts:

- ordinary localization of the homotopy category as the SCT localization;
- strict equality or strict isomorphism as a fake equivalence-edge predicate;
- `PUnit`, `True`, or arbitrary inhabited data for `Inverts` or the universal property;
- declaring every functor to invert every collection without a groupoid target theorem;
- treating the first three localization-candidate fields as sufficient without a universal
  property;
- adding derived-category claims before chain complexes, quasi-isomorphisms, and stable
  ∞-categorical structure are present.

## Expected implementation

A completed implementation should provide:

1. a concrete morphism-collection representation as a subobject of `Map([1],C)`;
2. an inversion predicate using invertible arrows/equivalence edges in the target;
3. `Fun_W(C,D)` as a full sub-quasicategory of `Fun(C,D)`;
4. a precomposition comparison `Fun(C[W⁻¹],D) → Fun_W(C,D)`;
5. an equivalence or mapping-anima equivalence proving the universal property;
6. projections closing `localizationDesc`, `localizationDescBeta`, and `localizationDescUniq`;
7. groupoid completion as localization at all morphisms;
8. no use of ordinary homotopy-category localization as a replacement for quasicategorical
   localization.
