# Functor quasicategory and bicategorical 2-cell bridge blueprint

## Project overview

This project connects two presentations that already appear in the SCT model work:

```text
Fun(C,D) := D^C                       -- simplicial internal hom, a quasicategory
NatTrans F G := F ⟶ G                 -- a 2-cell in mathlib's bicategory of quasicategories
NatIso F G := invertible such 2-cell
```

The model files need these presentations to agree.  A raw edge in the functor quasicategory
`Fun(C,D)` should give a bicategorical 2-cell between the endpoint functors, and invertible edges in
`Fun(C,D)` should correspond to invertible bicategorical 2-cells.  Conversely, a bicategorical
2-cell should have a representative edge in `Fun(C,D)` so that SCT declarations such as
`natTransObject`, `natTransUnderlyingArrow`, mapping anima, localization, and pullback comparison
objects can be interpreted without local placeholder data.

Most remaining work is an upstream mathlib project.  InternalMath now has a small local wrapper for
the upstream internal-hom quasicategory instance; the remaining temporary declarations concern the
vertex/edge/2-cell bridge.

## Internal-hom closure in mathlib master

Mathlib now supplies the inner-anodyne pushout-product argument in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct` and, in particular,
instances of the following shape:

```lean
instance {A X : SSet.{u}} [SSet.Quasicategory X] :
    SSet.Quasicategory ((ihom A).obj X)
```

It also proves related inner-fibration stability statements for internal homs, for example that
`(ihom X).map p` is an inner fibration when `p` is an inner fibration.

That PR is enough to bundle `Fun(C,D)` as a quasicategory:

```lean
⟨(ihom C.obj).obj D.obj, inferInstance⟩
```

It is not enough by itself to fill the SCT bridge.  It does not identify:

- vertices of `D^C` with bundled quasicategory morphisms `C ⟶ D` in the form needed by the SCT
  model;
- raw edges of `D^C` with bicategorical 2-cells in `SSet.QCat`;
- homotopy-category morphisms in `Ho(D^C)` with representatives by single edges;
- equivalence edges of `D^C` with invertible bicategorical 2-cells;
- vertical composition, whiskering, and horizontal composition of bicategorical 2-cells with the
  corresponding edge and simplex operations in the internal hom.

InternalMath exposes this through `InternalMath/SCT/IML/Model/FunctorQuasicategory.lean` as
`SCTFunctorQuasicategory.obj`.

## Existing InternalMath declarations involved

SCT model declarations in `InternalMath/SCT/Model.lean`:

- `SCTModelHelpers.funCat`;
- `SCTModelHelpers.functorVertex`;
- `SCTModelHelpers.NatTrans`;
- `SCTModelHelpers.NatIso`;
- the generated model field `natTransObject`;
- conversion helpers between local `NatIso` and generated `ModelNatIso` data.

Related blueprints:

- `Docs/IML/Model/MaximalKanCoreMappingAnimaBlueprint.md` uses this bridge to define mapping
  anima as maximal cores of functor quasicategories.
- `Docs/IML/Model/SegalCompositionBlueprint.md` uses this bridge for comparison data and the
  `Fun([1],[1])` presentation of `[2]`.
- `Docs/IML/Model/IsoRezkModelBlueprint.md` uses this bridge to build `Iso(C)` as a full
  subcategory of `Fun([1],C)` and to compare raw invertible edges with bicategorical `NatIso` data.
- `Docs/IML/Model/LocalizationBlueprint.md` uses this bridge for inverting-functor subcategories.
- `Docs/IML/Model/FibrationStablePullbacksBlueprint.md` uses this bridge for coherent cone
  comparisons in mapping-anima universal properties.

## Mathematical targets

### Target A: functor quasicategory package

Define a reusable bundled functor quasicategory:

```lean
QCat.functorQCat (C D : SSet.QCat) : SSet.QCat
```

with underlying simplicial set `(ihom C.obj).obj D.obj`, using the mathlib quasicategory instance
for internal homs.  InternalMath's current wrapper is `SCTFunctorQuasicategory.obj`; an upstream
`QCat.functorQCat` API would avoid local naming and add simp lemmas for rewriting through the
bundle.

### Target B: vertices are strict functors

Construct an equivalence between vertices of `Fun(C,D)` and strict functors `C ⟶ D`.

The forward direction sends a strict functor to the vertex obtained by currying
`C.obj ≅ Δ[0] × C.obj → D.obj`.  This is the role of `SCTModelHelpers.functorVertex`.

The reverse direction evaluates a vertex of `D^C`, equivalently a map `Δ[0] → D^C`, by uncurrying to
`Δ[0] × C.obj → D.obj` and composing with the unit isomorphism.  The API should include β/η lemmas
identifying the two round trips.

Expected declarations:

```lean
QCat.functorVertex     (F : C ⟶ D) : (QCat.functorQCat C D).obj _⦋0⦌
QCat.functorOfVertex   (x : (QCat.functorQCat C D).obj _⦋0⦌) : C ⟶ D
QCat.functorVertexEquiv : (C ⟶ D) ≃ (QCat.functorQCat C D).obj _⦋0⦌
```

### Target C: raw internal-hom edges give bicategorical 2-cells

An edge in `Fun(C,D)` from the vertex of `F` to the vertex of `G` should determine a morphism
`F ⟶ G` in the hom-category of the strict bicategory of quasicategories.  Since the strict
bicategory is built from the homotopy category of `D^C`, this map should be the homotopy-category
constructor for an edge, transported along the vertex equivalence from Target B.

Expected declaration shape:

```lean
QCat.edgeToTwoCell
  {F G : C ⟶ D}
  (e : SSet.Edge (QCat.functorVertex F) (QCat.functorVertex G)) : F ⟶ G
```

The API should include the identity edge and composition/2-simplex compatibility:

```text
edgeToTwoCell(id edge) = 𝟙 F
edgeToTwoCell(composite edge from a 2-simplex) =
  edgeToTwoCell(first edge) ≫ edgeToTwoCell(second edge)
```

### Target D: bicategorical 2-cells have edge representatives

For model constructions such as `natTransObject`, a bicategorical 2-cell needs a chosen edge
representative in `Fun(C,D)`.  The hom-categories in the strict bicategory are homotopy categories
of internal homs, so this requires a theorem that morphisms in the homotopy category of a
quasicategory are represented by single edges.

Mathlib already has relevant ingredients for 2-truncated quasicategories in
`Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated`, including a homotopy category whose
morphisms are edge homotopy classes.  The bridge should connect that API to the `hoFunctor` /
`HomotopyCategory` construction used by `QCat.strictBicategory`, or add the needed representative
lemma directly for the hom-category used by the bicategory.

Expected declaration shape:

```lean
QCat.twoCellRepresentative
  {F G : C ⟶ D} (α : F ⟶ G) :
  SSet.Edge (QCat.functorVertex F) (QCat.functorVertex G)

QCat.edgeToTwoCell_twoCellRepresentative
  (α : F ⟶ G) : QCat.edgeToTwoCell (QCat.twoCellRepresentative α) = α
```

This choice can be noncomputable.

### Target E: invertible 2-cells and equivalence edges

The model uses:

```lean
NatIso F G := (α : F ⟶ G) × IsIso α
```

Mapping anima and `Iso(C)` use equivalence edges in quasicategories.  The bridge should relate
these two notions in `Fun(C,D)`.

Expected declaration shapes:

```lean
QCat.edgeToTwoCell_isIso_of_equivalenceEdge
  (e : SSet.Edge (QCat.functorVertex F) (QCat.functorVertex G))
  (he : SSet.EquivalenceEdge e) : IsIso (QCat.edgeToTwoCell e)

QCat.equivalenceEdge_twoCellRepresentative_of_isIso
  (α : F ⟶ G) [IsIso α] :
  SSet.EquivalenceEdge (QCat.twoCellRepresentative α)
```

The exact predicate name should follow the upstream equivalence-edge API, especially the material
from mathlib PR #35287 or its successor.  The proof should use the standard fact that equivalences
in the homotopy category of a quasicategory are represented by equivalence edges.

### Target F: whiskering and horizontal composition

SCT needs vertical composition, pre/post-whiskering, and horizontal composition of `NatIso`s.  The
bridge should show that the bicategorical operations agree with internal-hom operations:

- postcomposition `Fun(C,D) → Fun(C,E)` induced by `D ⟶ E`;
- precomposition `Fun(D,E) → Fun(C,E)` induced by `C ⟶ D`;
- horizontal composition as the composite of pre/post-whiskering;
- preservation of equivalence edges by these maps.

This supplies the semantic link between raw mapping-anima edges and the `NatIso` operations used by
`InternalMath.SCT.Model`.

### Target G: `natTransObject` adapter

After Targets B--E, implement the SCT model field `natTransObject`: given a bicategorical 2-cell
`α : F ⟶ G`, choose `QCat.twoCellRepresentative α`, view it as a vertex of the arrow category of
`Fun(C,D)`, and package it in the source/target fiber defining `natTransCat C D F G`.

The required proof obligations are endpoint compatibility with `F` and `G`, plus compatibility with
`functorFromObject` and `natTransUnderlyingArrow` from the SCT specification.

## Recommended implementation phases

### Phase 1: expose the internal-hom instance

Done locally for InternalMath: `SCTFunctorQuasicategory.obj` bundles the upstream mathlib instance.
A future upstream `QCat.functorQCat` wrapper and simp lemmas would let the SCT files drop the local
adapter.

### Phase 2: vertex equivalence

Build the equivalence between strict functors and vertices of the internal hom.  This phase should
be mostly formal monoidal-closed bookkeeping: curry/uncurry, the unit object, and endpoint simp
lemmas.

### Phase 3: edge-to-2-cell map

Define the map from raw internal-hom edges to bicategorical 2-cells via the homotopy-category
constructor.  Prove identity and 2-simplex composition compatibility.

### Phase 4: representative theorem

Prove that every bicategorical 2-cell has a representative edge.  If possible, reuse the
2-truncated quasicategory homotopy-category API; otherwise prove the representative theorem for the
`hoFunctor` hom-category used by `QCat.strictBicategory`.

### Phase 5: invertibility/equivalence-edge theorem

Relate equivalence edges in `Fun(C,D)` to `IsIso` 2-cells.  This phase depends on the preferred
mathlib equivalence-edge predicate and inverse-edge API.

### Phase 6: operation compatibility

Prove compatibility with vertical composition, pre/post-whiskering, and horizontal composition, and
prove preservation of equivalence edges under these operations.

### Phase 7: replace InternalMath placeholders

Use the bridge API to replace:

- `sctModel.natTransObject`;
- mapping-anima and localization bridge placeholders that need vertex/edge/2-cell data.

## Anti-patterns

Do not use strict equality of functors as a substitute for bicategorical 2-cells.

Do not define `NatIso` by raw inverse-edge data without proving compatibility with the strict
bicategory's `IsIso` notion.

Do not assume a chosen edge representative is canonical.  The representative can be noncomputable,
and later constructions should be invariant under the homotopy relation.

Do not duplicate the internal-hom quasicategory proof; use the upstream instance from
`AnodyneExtensions.Inner.PushoutProduct`.

Do not hide this bridge inside `InternalMath/SCT/Model.lean` as local `sorry`s.  The result is a
reusable mathlib-level interface for quasicategories, functor quasicategories, and the strict
bicategory.

## Expected result

A completed bridge should make the following statement precise and usable in Lean:

```text
The hom-category between quasicategories C and D in mathlib's strict bicategory is the homotopy
category of the functor quasicategory Fun(C,D), with objects strict functors, morphisms represented
by edges, and isomorphisms represented by equivalence edges.
```

That API would unlock the `natTransObject` field in `InternalMath/SCT/Model.lean`, remove the
remaining vertex/edge bridge assumptions, and provide the common bridge needed by mapping anima,
localization, Iso/Rezk, Segal comparison data, and homotopy-pullback cone comparisons.
