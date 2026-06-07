# Segal composition and arrow calculus blueprint

## Project overview

Composition in a quasicategory is encoded by filling a triangle whose two short edges are
composable arrows. The composite is the long edge of a chosen filler, while units and associativity
hold by coherent comparison data rather than by strict equality. This project turns that geometric
picture into the model fields used for SCT composition.

## Project dependencies

- Can start independently of the other `Docs/IML/Model` blueprints.
- Uses `InternalMath/SCT/IML/Model/FiniteShapes.lean` for simplex and square shapes, and mathlib's
  quasicategory horn-filling API for fillers.
- Downstream projects depending on this blueprint include `IsoRezkModelBlueprint.md`, especially
  its invertible-arrow unit comparison phase.

Workshop blueprint for the Segal-composition model scaffold.

Scope: this note expands the project around the SCT composition fields in
`InternalMath/SCT/Model.lean`. The companion Lean scaffold is
`InternalMath/SCT/IML/Model/SegalComposition.lean`. The finite shape package it uses is
`InternalMath/SCT/IML/Model/FiniteShapes.lean`.

## Short version

For a quasicategory `C`, composition is modeled by filling inner horns

```text
Λ[2,1] -> C
```

or equivalently by extending a strictly composable pair of interval-shaped arrows to a `2`-simplex
`[2] -> C`. The composite is the `0 -> 2` face of a chosen filler.

The main rule for this project is that filler choices are not unique on the nose. Unit,
associativity, and naturality fields must be comparison data, matching the book and the model's
bicategorical `NatIso` representation.

## Existing SCT declarations involved

Shape and Segal fields:

- `simplex2Cat`;
- `simplex2Face01`, `simplex2Face12`, `simplex2Face02`;
- `squareCat`, `squareLowerTriangle`, `squareUpperTriangle`;
- `squareRestriction`, `squareExtension`;
- `segalRestriction`, `segalExtension`;
- `segalUnit`, `segalCounit`.

Composition fields:

- `compositeSourceCompat`;
- `compositeTargetCompat`;
- `composeLeftUnit`;
- `composeRightUnit`;
- `composeAssoc`.

Bicategorical/naturality fields affected later:

- `horizCompIdId`;
- `horizCompCompComp`;
- `horizCompLeftId`;
- `horizCompRightId`;
- `assocFunctorNaturality`.

Invertible-arrow fields depending on this project:

- `invertibleMorphismLeftUnit`;
- `invertibleMorphismRightUnit`.

## Foundation from `FiniteShapes.lean`

The finite-shape package supplies checked Lean declarations for:

- `[0]`, `[1]`, `[2]` as bundled quasicategories;
- maps induced by simplex-category morphisms;
- cofaces and codegeneracies;
- the three oriented faces of `[2]`:
  - `simplex2Face01 : [1] -> [2]`;
  - `simplex2Face02 : [1] -> [2]`;
  - `simplex2Face12 : [1] -> [2]`;
- endpoint orientation lemmas for all three faces;
- the degeneracy `[1] -> [0]` and its endpoint lemmas;
- `[1] × [1]`, its projections, vertices, horizontal edges, vertical edges, and its identification
  with the nerve of the product poset;
- span and cospan shapes as nerves of mathlib walking shapes.

The Segal project can use these declarations without carrying the finite-shape bookkeeping. The
scaffold also has a `ModelBridge` namespace for the generated model's presentation
`simplex2Cat := Fun([1],[1])`. The bridge records the identification between `[2]` and monotone
families of endomaps of `[1]`; `Model.lean` refers to those project-file declarations for the three
`simplex2Face*` maps and their endpoint comparisons.

## Mathematical targets

### Target A: composable pairs as inner horns

Represent a composable pair of interval-shaped arrows in `C` as:

```lean
f : [1] -> C
g : [1] -> C
target f = source g
```

This is the data of a map from the inner horn `Λ[2,1]` to `C`, with `f` on the `0 -> 1` face and
`g` on the `1 -> 2` face. Geometrically, the horn is a triangle whose two short edges are known and
whose long edge is missing.

The scaffold uses a strict endpoint equality because it describes a strict horn map. This equality
should not be generalized into strict equality for synthetic comparison fields.

### Target B: chosen fillers and composites

For every composable pair, choose a filler:

```lean
σ : [2] -> C
σ|01 = f
σ|12 = g
```

Then define the composite as:

```lean
f ; g := σ|02
```

The chosen `2`-simplex is the witness that the long edge really composes the two short edges. A
different filler might choose a different long edge, so later fields must provide comparison data
rather than proving all choices definitionally equal.

The intended proof constructs the horn map into `C` and applies `SSet.Quasicategory.hornFilling`.
The proof should be noncomputable because it chooses a filler.

The scaffold already proves, for any supplied `TriangleFiller`, that the composite has the source of
`f` and target of `g` using only finite-shape orientation lemmas.

### Target C: unit comparisons

For an interval arrow `f : [1] -> C`, define identity arrows by degeneracy:

```text
id_x := [1] -> [0] -> C
```

Then construct comparison data:

```text
id_source(f) ; f  ≃ f
f ; id_target(f)  ≃ f
```

These comparisons say that composing with a degenerate edge behaves like doing nothing. In a
quasicategory this is again witnessed by fillers and coherent comparisons, so the model should
package bicategorical natural-isomorphism data, not strict equality of chosen fillers.

### Target D: associativity comparison

For a composable triple `f,g,h`, compare:

```text
(f ; g) ; h  ≃  f ; (g ; h)
```

The proof should use a `3`-simplex or an equivalent pasting argument in a quasicategory. The result
must be packaged as the model's comparison data.

### Target E: square and horizontal-composition calculus

The square shape `[1] × [1]` should support the later horizontal-composition fields. The first
phase only needs orientation lemmas and projection beta rules. Later phases should add:

- lower and upper triangle inclusions;
- restriction of square data to composable arrows;
- extension/filling operations;
- compatibility of square pasting with Segal composition;
- horizontal composition of bicategorical 2-cells.

## Dependencies

Already available:

- `InternalMath/SCT/IML/Model/FiniteShapes.lean` for the finite shape maps and endpoint lemmas;
- mathlib's quasicategory horn-filling API;
- mathlib's strict bicategory on `SSet.QCat` for eventual comparison data.

Still needed:

- a concrete horn-map construction for `Λ[2,1] -> C` from a `ComposablePair`;
- adapters from chosen fillers to SCT `NatIso`/comparison fields;
- the functor-quasicategory bridge from
  `Docs/IML/Model/FunctorQuasicategoryBridgeBlueprint.md` if comparisons must be related to objects
  or edges of internal homs;
- PR #35287 or an equivalent inverse-edge API for the invertible-morphism unit fields.

## Recommended implementation phases

### Phase 1: horn construction and filler

- Construct the inner horn `Λ[2,1] -> C` from `ComposablePair C`.
- Apply quasicategory horn filling to produce `TriangleFiller`.
- Keep the chosen filler noncomputable.
- Retain the existing source/target lemmas for composites.

### Phase 2: units

- Define left and right unit composable pairs using `[1] -> [0]`.
- Build comparison data between chosen composites and the original arrow.
- Package the result in the model's `NatIso` format.

### Phase 3: associativity

- Build the two composites for a composable triple.
- Use a `3`-simplex or pasting theorem to compare them.
- Package the result as bicategorical comparison data.

### Phase 4: square calculus

- Add lower/upper triangle inclusions into `[1] × [1]`.
- Relate square restrictions to pairs of composable arrows.
- Use square fillers to support horizontal composition fields.

## Pitfalls

- Do not assert strict uniqueness of quasicategory fillers.
- Do not close unit or associativity fields with equality-to-`NatIso` unless the field is genuinely
  strict by construction.
- Do not use ordinary category composition in the homotopy category as a replacement for the
  quasicategory filler data.
- Keep interval endpoint equalities limited to strict shape maps and horn construction.

## Expected scaffold shape

The companion file should reserve its `sorry` markers for the mathematical gaps in this project:

- chosen horn fillers;
- arrow comparison data;
- associativity comparison data;
- the generated-model bridge between `[2]` and `Fun([1],[1])`.

Finite shape orientation lemmas belong in `InternalMath/SCT/IML/Model/FiniteShapes.lean`, not as
new admissions in the Segal file.

## Companion Lean scaffold

The companion file `InternalMath/SCT/IML/Model/SegalComposition.lean` defines the namespace
`SCTSegalCompositionSkeleton`.  Its checked endpoint lemmas for identities and supplied triangle
fillers have no `sorry`s.  The Lean `sorry` markers in the file are exactly these SCT project seams:

```lean
SCTSegalCompositionSkeleton.chosenFiller
SCTSegalCompositionSkeleton.ArrowComparison
SCTSegalCompositionSkeleton.AssociativityComparison
SCTSegalCompositionSkeleton.ModelBridge.quasicategoryInternalHom
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face01
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face12
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face02
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face01Zero
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face01One
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face12Zero
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face12One
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face02Zero
SCTSegalCompositionSkeleton.ModelBridge.simplex2Face02One
```

## Informal proof or construction for each Lean `sorry`

This section tracks every `sorry` present in
`InternalMath/SCT/IML/Model/SegalComposition.lean`.  If the Lean scaffold changes, update this list
in the same commit.

### `chosenFiller`

A `ComposablePair C` is a strict map from the inner horn `Λ[2,1]` to `C`: put `p.first` on the
`0 → 1` face, `p.second` on the `1 → 2` face, and use `p.matching` for the common vertex.  Since
`C` is a quasicategory, the inner horn inclusion has a filler.  Choose such a filler
noncomputably, take its underlying `2`-simplex as `TriangleFiller.simplex`, and record the two face
restriction equations as `face01` and `face12`.

### `ArrowComparison`

This is an API target rather than a theorem.  Replace it by the model's comparison data between two
interval-shaped arrows.  The intended implementation is either bicategorical `NatIso` between the
corresponding functors `[1] → C`, or equivalence-edge data in the functor quasicategory
`Fun([1], C)` after the internal-hom bridge exists.  This comparison type supplies the unit and
associativity fields; it should not collapse to strict equality of chosen fillers.

### `AssociativityComparison`

For a composable triple `f,g,h`, build the two composites `(f ; g) ; h` and `f ; (g ; h)` using the
chosen fillers.  The comparison comes from the standard quasicategory associativity argument: form
the relevant boundary or inner horn in dimension `3`, use horn filling or pasting to obtain a
coherent `3`-simplex, and read off an invertible comparison between the two long edges.  Package the
result using `ArrowComparison`.

### `ModelBridge.quasicategoryInternalHom`

Use the standard theorem that if `D` is a quasicategory, then the simplicial internal hom
`D.obj ^ C.obj` is a quasicategory.  In mathlib notation this is the quasicategory structure on
`(ihom C.obj).obj D.obj`.  This theorem should be shared with the mapping-anima and localization
scaffolds, since all three need the same functor-quasicategory API.

### `ModelBridge.simplex2Face01`

Construct the edge of `Fun([1],[1])` from the constant-zero endomap to the identity endomap by
currying the monotone map `[1] × [1] → [1]` given by `min`.  Under the internal-hom adjunction, this
monotone family gives a map `[1] → Fun([1],[1])`, hence a morphism
`intervalQCat ⟶ funCat intervalQCat intervalQCat`.

### `ModelBridge.simplex2Face12`

Construct the edge from the identity endomap to the constant-one endomap by currying the monotone
map `[1] × [1] → [1]` given by `max`.  The endpoint at `0` is the identity family and the endpoint
at `1` is the constant-one family.

### `ModelBridge.simplex2Face02`

Construct the edge from the constant-zero endomap to the constant-one endomap by currying the
projection family `[1] × [1] → [1]` used by the `[2] ≃ Fun([1],[1])` bridge.  This is the long face
of the triangle in the generated model's presentation.

### `ModelBridge.simplex2Face01Zero`

After `simplex2Face01` is built from the `min` family, precomposing with the zero endpoint of the
outer interval gives the constant-zero endomap.  The formal proof should identify the supplied
`simplex2Id0` with that constant-zero functor and then use the internal-hom β rule to build the
`NatIso`.  The declaration as written treats `simplex2Id0` as an arbitrary argument, so the final
API should add the needed identification field or replace the argument by the canonical functor.

### `ModelBridge.simplex2Face01One`

Precomposing the `min` family with the one endpoint gives the identity endomap.  The formal proof
should identify the supplied `simplex2Can` with the canonical identity endomap and then use the
internal-hom β rule.  As above, the scaffold type needs the endpoint-identification hypothesis or a
canonical endpoint term.

### `ModelBridge.simplex2Face12Zero`

Precomposing the `max` family with the zero endpoint gives the identity endomap.  The proof should
identify `simplex2Can` with the canonical identity endomap and then apply the internal-hom β rule
for the curried `max` family.

### `ModelBridge.simplex2Face12One`

Precomposing the `max` family with the one endpoint gives the constant-one endomap.  The proof
should identify `simplex2Id1` with the canonical constant-one functor and then apply the
internal-hom β rule.

### `ModelBridge.simplex2Face02Zero`

Precomposing the long-face family with the zero endpoint gives the constant-zero endomap.  The proof
should identify `simplex2Id0` with the canonical constant-zero functor and then use the β rule for
the curried projection family.

### `ModelBridge.simplex2Face02One`

Precomposing the long-face family with the one endpoint gives the constant-one endomap.  The proof
should identify `simplex2Id1` with the canonical constant-one functor and then use the β rule for
the curried projection family.
