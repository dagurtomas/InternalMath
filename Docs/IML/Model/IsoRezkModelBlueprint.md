# Invertible arrows, `Iso(C)`, and Rezk equivalence blueprint

## Project overview

The category `Iso(C)` should collect the invertible arrows of a synthetic category `C`. The Rezk
axiom says that sending an object of `C` to its identity arrow gives an equivalence
`C ≃ Iso(C)`. This project builds the quasicategory model of invertible arrows and the comparison
showing that it has the expected Rezk behavior.

## Project dependencies

- The edge-level audit and interval-arrow adapter phases can start from the finite-shape scaffold
  and the incoming inverse-edge API from mathlib PR #35287.
- The unit comparison phase depends on `Docs/IML/Model/SegalCompositionBlueprint.md`, because it
  uses the chosen composition operation for invertible arrows.
- The object collection, `Iso(C)`, and Rezk comparison phases depend on
  `Docs/IML/Model/FunctorQuasicategoryBridgeBlueprint.md` for the bridge from bicategorical
  2-cells to edges of functor quasicategories, and on
  `Docs/IML/Model/MaximalKanCoreMappingAnimaBlueprint.md` for equivalence-edge, maximal-core,
  mapping-anima, and groupoid-core adapters.

Workshop blueprint for the invertible-arrow and Rezk-equivalence model scaffold.

Scope: this note expands the project around invertible interval-shaped arrows, the category of
isomorphisms `Iso(C)`, and the Rezk comparison field in `InternalMath/SCT/Model.lean`. The
companion Lean scaffold is `InternalMath/SCT/IML/Model/IsoRezkModel.lean`.

## Short version

The intended model interpretation is:

```text
InvertibleMorphism(C,f) := inverse-edge data for the edge classified by f : [1] -> C
Iso(C)                  := full subcategory of Fun([1],C) on invertible arrows
rezkEquiv(C)            := quasicategorical equivalence C ≃ Iso(C)
```

This project should use the incoming edge-level API from mathlib PR #35287, but most SCT work uses
higher-level adapters above that API. The PR supplies inverse-edge data in simplicial sets and the
coherent isomorphism simplicial set. It does not construct `Iso(C)` or prove the Rezk equivalence.

## Existing SCT declarations involved

Chapter 1 interval and invertible-arrow declarations:

- `InvertibleMorphismData` / `InvertibleMorphism`, a checked `syntax_def` Sigma package;
- `invertibleMorphismInverse`;
- `invertibleMorphismInverseSource`;
- `invertibleMorphismInverseTarget`;
- `invertibleMorphismLeftUnit`;
- `invertibleMorphismRightUnit`.

The projection declarations are admitted internal definitions for the package-projection API. The
generated model interface does not ask model providers for these fields.

Chapter 1 `Iso(C)` and Rezk fields:

- `invertibleMorphismObjectPackage`;
- `invertibleMorphismObjects`;
- `isoCat`;
- `isoProjection`;
- `isoProjectionEmbedding`;
- `rezkEquiv`;
- `identityIsoFunctor`, `isoProjectionFunctor`, `rezkUnit`, `rezkCounit`.

Related model scaffolds:

- finite shape maps from `InternalMath/SCT/IML/Model/FiniteShapes.lean`;
- Segal composition helpers from `InternalMath/SCT/IML/Model/SegalComposition.lean`;
- maximal-core/equivalence-edge work in `InternalMath/SCT/IML/Model/MappingAnima.lean`;
- the bicategorical `NatTrans`/local `NatIso` skeleton in `InternalMath/SCT/Model.lean`.

## What PR #35287 covers

The PR titled

```text
feat(AlgebraicTopology/SimplicialSet): define isomorphisms in simplicial sets,
and the coherent isomorphism simplicial set
```

covers the low-level simplicial-set part of this project.

Expected incoming API:

- `SSet.Edge.InvStruct hom`, with fields:
  - inverse edge `inv`;
  - `homInvId : CompStruct hom inv (id source)`;
  - `invHomId : CompStruct inv hom (id target)`;
- identity inverse structures;
- inverse-of-inverse;
- preservation of inverse structures under simplicial maps;
- transport of inverse structures along equality of underlying one-simplices;
- `SSet.coherentIso`, the nerve of the walking isomorphism;
- the source vertex, target vertex, forward edge, and backward edge of `coherentIso`;
- inverse-edge data for the forward edge of `coherentIso`;
- a theorem saying that an edge equal to the image of the forward coherent-isomorphism edge has
  inverse-edge data.

Local consequence: once the PR lands, replace
`SCTIsoRezkModelSkeleton.IncomingPR35287.EdgeInvStruct` by `SSet.Edge.InvStruct` and delete the
local duplicate identity/symmetry helpers.

## What PR #35287 does not cover

The following remain InternalMath/SCT projects.

### A. Interval-functor adapters

SCT invertible morphisms are interval-shaped functors:

```lean
f : Functor intervalCat C
```

In the model these are maps `[1] -> C`. The PR gives inverse data for an edge of a simplicial set.
Required adapters:

```lean
arrowEdge        : ([1] -> C) -> SSet.Edge x y
arrowOfSimplex   : C_1 -> ([1] -> C)
inverseArrow     : Edge.InvStruct (arrowEdge f) -> ([1] -> C)
```

The scaffold already defines the easy underlying one-simplex and inverse-arrow construction. The
endpoint comparisons are:

```text
source(inverse f) = target(f)
target(inverse f) = source(f)
```

These comparisons involve interval-shaped functors, the SCT source/target operations, and the raw
edge endpoints.

### B. Compatibility with chosen Segal composition

The PR provides two raw `2`-simplices witnessing inverse composites. SCT fields ask for unit
comparisons involving the model's chosen composition operation. In other words, the inverse edge
from the PR must be compared with the composite chosen by the Segal-composition model code:

```lean
composeComposableMorphism C f (inverse f) ...
composeComposableMorphism C (inverse f) f ...
```

Those comparisons require the Segal-composition package. They should not be replaced by strict
uniqueness of fillers.

### C. Object collection of invertible arrows

The field

```lean
invertibleMorphismObjectPackage
```

requires an object collection in `Fun([1], C)` whose members are exactly the invertible arrows. The
collection is the semantic version of the predicate "this arrow has an inverse". Building it means
connecting the raw edge-level inverse data to vertices of the functor quasicategory.

This needs:

- the functor-quasicategory/internal-hom API;
- the bridge between vertices of `Fun([1], C)` and interval-shaped functors;
- object-collection and full-subcategory semantics;
- equivalence between object-collection membership and inverse-edge data.

The PR does not construct any of this.

### D. `Iso(C)` as a full subcategory

The internal spec defines:

```lean
isoCat C := fullSubcategory (funCat intervalCat C) (invertibleMorphismObjects C)
```

The model must build the corresponding full subquasicategory and its inclusion into `Fun([1], C)`.
Fullness means that once the invertible arrows have been chosen as objects, the morphisms between
them are inherited from the ambient arrow category. The PR supplies the low-level predicate/data
used to define the object collection.

### E. Rezk equivalence

The field

```lean
rezkEquiv : CatEquiv C (isoCat C)
```

is a high-level quasicategorical equivalence. It depends on the completed `Iso(C)` construction and
on the model's bicategorical `NatIso`/`CatEquiv` representation. PR #35287 does not prove this.

### F. Groupoid interval equivalence

The model fields around groupoids, especially `groupoidIntervalEquiv`, require the maximal-core and
groupoid/anima comparison projects. The coherent-isomorphism API is useful input, but it is not the
whole groupoid interval theorem.

## Recommended implementation phases

### Phase 1: replace local edge inverse data after PR #35287 lands

- Import the new mathlib file containing `SSet.Edge.InvStruct` and `SSet.coherentIso`.
- Replace the local `IncomingPR35287.EdgeInvStruct` scaffold.
- Add compatibility aliases if names differ from the scaffold.
- Prove that simplicial maps preserve invertible edges using the PR theorem.

Expected result: the raw edge-level inverse data in `Model.lean` and the mapping-anima scaffold can
use a shared upstream structure.

### Phase 2: interval-arrow adapter

- Define the one-simplex/edge classified by a map `[1] -> C`.
- Define the inverse interval arrow from `Edge.InvStruct`.
- Prove source and target endpoint comparisons for the inverse interval arrow.
- Connect this adapter to the generated SCT fields `invertibleMorphismInverseSource` and
  `invertibleMorphismInverseTarget`.

This phase can begin once the finite-shape endpoint lemmas are stable.

### Phase 3: Segal unit comparisons

- Use the Segal-composition scaffold to identify the raw inverse triangles with the chosen
  composites.
- Prove the left and right unit comparison fields for invertible morphisms.
- Package the comparisons as bicategorical `NatIso` data, matching the SCT model interpretation.

This phase should wait for the Segal-composition project.

### Phase 4: object collection and full subcategory

- Define the object collection of invertible arrows in `Fun([1], C)`.
- Build the full subquasicategory `Iso(C)`.
- Prove the inclusion into `Fun([1], C)` is the intended full-subcategory inclusion.
- Fill or refine `invertibleMorphismObjectPackage`.

This phase depends on the functor-quasicategory bridge and full-subcategory model scaffold.

### Phase 5: Rezk comparison

- Define the identity-isomorphism functor `C -> Iso(C)`.
- Define the projection/backward functor `Iso(C) -> C`.
- Prove the unit and counit as bicategorical natural isomorphisms.
- Package the result as `CatEquiv C (isoCat C)`.

Do not attempt this phase by defining `Iso(C)` from the desired equivalence.

## Pitfalls

- Do not define `Iso(C)` by assuming `rezkEquiv`; that is circular.
- Do not turn inverse-edge data into strict equality of arrows or strict uniqueness of fillers.
- Do not conflate bicategorical invertible 2-cells with raw edges until the functor-quasicategory
  bridge is available.
- Do not treat the coherent isomorphism simplicial set as a replacement for the full maximal-core or
  mapping-anima construction.

## Expected scaffold shape

The companion file should reserve its `sorry` markers for the SCT work in this scaffold. It should
identify which declarations are local shapes for PR #35287 and which ones are genuine
InternalMath/SCT obligations.

## Companion Lean scaffold

The companion file `InternalMath/SCT/IML/Model/IsoRezkModel.lean` defines the namespace
`SCTIsoRezkModelSkeleton`.  The local `IncomingPR35287.EdgeInvStruct`, `id`, and `symm` declarations
are temporary API shapes for the incoming PR and carry no `sorry`s.  The Lean `sorry` markers in the
file are exactly these SCT project seams:

```lean
SCTIsoRezkModelSkeleton.IntervalArrow.inverseEndpointComparisons
SCTIsoRezkModelSkeleton.SegalInterface.InverseUnitComparisons
SCTIsoRezkModelSkeleton.IsoCategory.arrowFunctorQCat
SCTIsoRezkModelSkeleton.IsoCategory.InvertibleArrowObjectCollection
SCTIsoRezkModelSkeleton.IsoCategory.FullSubcategoryWitness
SCTIsoRezkModelSkeleton.IsoCategory.candidate
SCTIsoRezkModelSkeleton.Rezk.EquivalenceData
SCTIsoRezkModelSkeleton.Rezk.comparison
```

## Informal proof or construction for each Lean `sorry`

This section tracks every `sorry` present in `InternalMath/SCT/IML/Model/IsoRezkModel.lean`.  If the
Lean scaffold changes, update this list in the same commit.

### `IntervalArrow.inverseEndpointComparisons`

An interval-shaped arrow `f : [1] → C` classifies a one-simplex whose endpoints are the source and
target of `f`.  The inverse-edge data from PR #35287 gives an inverse edge with source equal to the
target of `f` and target equal to the source of `f`.  Turn that inverse edge back into an
interval-shaped arrow using `ofSimplex`.  The endpoint comparisons then follow by unfolding
`source`, `target`, `simplex`, `edge`, `inverseFromInvStruct`, and the endpoint equations supplied
by the incoming edge API, plus the finite-shape vertex orientation lemmas.

### `SegalInterface.InverseUnitComparisons`

This placeholder should become a structure carrying the two unit comparison fields required by SCT:
`f ; f⁻¹ ≃ id` and `f⁻¹ ; f ≃ id`, packaged as the model's bicategorical `NatIso` data.  The raw
triangles come from `h.homInvId` and `h.invHomId` in the inverse-edge structure.  The missing work
compares those raw triangles with the Segal-composition package's chosen composites, then transports
the result through the interval-arrow endpoint adapter.

### `IsoCategory.arrowFunctorQCat`

Define the arrow functor quasicategory as the simplicial internal hom `Fun([1], C)`, equivalently
`C.obj ^ Δ[1]` with the bundled quasicategory structure.  The proof obligation is the standard
internal-hom theorem for quasicategories: if `C` is a quasicategory, then the simplicial internal
hom from any simplicial set into `C` is a quasicategory.  This should use the same API as the
Segal-composition and localization scaffolds.

### `IsoCategory.InvertibleArrowObjectCollection`

Use the vertex equivalence between `Fun([1], C)` and interval-shaped arrows `[1] → C`.  The object
collection consists of those vertices whose corresponding edge has inverse-edge data, endpoint
comparisons, and Segal unit comparisons.  Equivalently, it is the pullback of the equivalence-edge
or invertible-arrow predicate along the map from vertices of the arrow functor quasicategory to
edges of `C`.

### `IsoCategory.FullSubcategoryWitness`

Apply the quasicategorical full-subcategory construction to the object collection from the previous
item.  The witness should include the inclusion `Iso(C) → Fun([1], C)`, the fact that its vertices
are exactly invertible arrows, and fullness: mapping spaces between chosen objects are inherited
from the ambient arrow functor quasicategory.

### `IsoCategory.candidate`

Take `obj` to be the full subquasicategory of `Fun([1], C)` on invertible arrows, `incl` to be the
full-subcategory inclusion, `objects` to be the invertible-arrow object collection, and
`fullSubcategory` to be the witness described above.  This construction depends on the functor
quasicategory, object-collection, and full-subcategory APIs rather than on the Rezk comparison.

### `Rezk.EquivalenceData`

Define the identity-isomorphism functor `C → Iso(C)` by sending an object to its degenerate identity
arrow.  Define the projection functor `Iso(C) → C` by taking the source, or equivalently the target,
of an invertible arrow, with the inverse-edge data giving the comparison.  The unit at an object is
identity data.  The counit at an invertible arrow is the coherent isomorphism connecting the arrow
to the identity arrow at its source or target.  Package the two functors and their unit/counit as
the model's `CatEquiv`/bicategorical natural-isomorphism data.

### `Rezk.comparison`

Instantiate `Rezk.EquivalenceData` for the candidate `Iso(C)` built above.  The proof should not
construct `Iso(C)` from the desired equivalence; it should first build the full subcategory of
invertible arrows and then apply the Rezk-completeness theorem for quasicategories, using the
coherent-isomorphism API and maximal-core/mapping-anima adapters.
