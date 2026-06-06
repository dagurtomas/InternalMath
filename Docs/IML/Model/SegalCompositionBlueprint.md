# Segal composition and arrow calculus blueprint

## Project overview

Composition in a quasicategory is encoded by filling a triangle whose two short edges are
composable arrows. The composite is the long edge of a chosen filler, while units and associativity
hold by coherent comparison data rather than by strict equality. This project turns that geometric
picture into the model fields used for SCT composition.

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
`g` on the `1 -> 2` face.

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

These comparisons should be bicategorical natural-isomorphism data in the model, not strict equality
of chosen fillers.

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
- the functor-quasicategory bridge if comparisons must be related to objects or edges of internal
  homs;
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
- associativity comparison data.

Finite shape orientation lemmas belong in `InternalMath/SCT/IML/Model/FiniteShapes.lean`, not as
new admissions in the Segal file.
