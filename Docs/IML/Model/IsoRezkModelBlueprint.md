# Invertible arrows, `Iso(C)`, and Rezk equivalence blueprint

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

These comparisons are about interval-shaped functors and the SCT source/target operations, not just
about the raw edge endpoints.

### B. Compatibility with chosen Segal composition

The PR provides two raw `2`-simplices witnessing inverse composites. SCT fields ask for unit
comparisons involving the model's chosen composition operation:

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

requires an object collection in `Fun([1], C)` whose members are exactly the invertible arrows. This
needs:

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
The PR supplies only the low-level predicate/data used to define the object collection.

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

This is mostly agent-friendly once the finite-shape endpoint lemmas are stable.

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

This is human-led and should not be attempted by defining `Iso(C)` from the desired equivalence.

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
