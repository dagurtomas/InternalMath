# Objectwise natural isomorphism internal blueprint

## Project overview

A natural transformation should be a natural isomorphism exactly when each of its components is an
invertible arrow. This project makes that principle usable inside SCT: it should expose componentwise
invertibility from a natural isomorphism and assemble a natural isomorphism from objectwise
invertibility evidence, without turning the statement into a strict equality or a vacuous package.

## Project dependencies

- The needed Chapter 1 APIs already exist in the SCT specification: `natTransComponent` and the
  invertible-arrow package from `Chapter1/CellsAndSegal.lean`.
- This dependency is about declaration order and package design, not about starting a separate
  Chapter 1 project.
- The package design has a circularity hazard: `NatIso` is used early in the specification, while
  invertible interval-shaped morphisms are defined later using `NatIso` comparisons. The first task
  is to choose a non-circular organization for the objectwise criterion.
- Downstream projects depending on this one include the Fundamental Theorem blueprint,
  postcomposition fully faithfulness, Rezk comparison work, and cocartesian-functor equivalence
  criteria.

Workshop blueprint for the objectwise natural-isomorphism package and its projection API.

Target modules:

```text
InternalMath/SCT/Spec/Prelude.lean
InternalMath/SCT/Spec/Chapter6/FundamentalTheorem.lean
```

Related modules:

```text
InternalMath/SCT/Spec/Chapter1/CellsAndSegal.lean
InternalMath/SCT/Spec/Chapter6/Definitions.lean
```

## Admissions in scope

```lean
SCT.ObjectwiseNatIsoData
SCT.objectwiseNatIsoComponent
```

The first declaration is an admitted `syntax_def` package in the prelude. The second declaration is
the projection used in Chapter 6 to extract the invertible component at an object.

Checked declarations already built around the package include:

```lean
SCT.NatIso
SCT.natIsoToNatTrans
SCT.natIsoObjectwise
SCT.natIsoObjectwiseComponent
SCT.objectwiseNatIsoComponentInvertible
SCT.natIsoOfObjectwise
```

The project should preserve these public names or provide a small compatibility layer.

## Mathematical target

The intended theorem is the objectwise criterion:

```text
α : F ⟶ G is a natural isomorphism
  iff
for every x : A, the component α_x : F x → G x is invertible.
```

In the current SCT notation the component is:

```lean
natTransComponent A C F G α x : Functor intervalCat C
```

and the target componentwise statement is:

```lean
InvertibleMorphism C (natTransComponent A C F G α x)
```

So the natural package shape one wants is morally:

```lean
(x : Obj A) → InvertibleMorphism C (natTransComponent A C F G α x)
```

The difficulty is import and declaration order: this expression mentions declarations from Chapter
1, while `NatIso` is introduced in the prelude before those declarations are in scope. The project is
therefore partly a design project: make this objectwise content explicit while keeping the early SCT
vocabulary book-faithful and non-circular.

## Design options

### Option A: refactor the declaration order

Move enough component and invertible-arrow vocabulary earlier that `ObjectwiseNatIsoData` can become
a checked `syntax_def` package directly.

This option is attractive because the package body is transparent and projections become simple. It
requires care because invertible interval-shaped morphisms use `NatIso` in their endpoint and unit
comparisons, so a naive move can create a definitional cycle.

### Option B: split primitive natural isomorphisms from the objectwise criterion

Keep a primitive or axiom-level `NatIso` notion in the early vocabulary, then prove an objectwise
criterion later in Chapter 6.

This option may match the book if natural isomorphisms are treated as primitive ambient structure in
Axiom A and the objectwise criterion is a later theorem. It should still provide checked adapters:

```lean
NatIso A C F G → ObjectwiseNatIso A C F G (natIsoToNatTrans A C F G α)
ObjectwiseNatIso A C F G α → NatIso A C F G
```

If this option is chosen, avoid leaving a hidden `True`-like package under the name
`ObjectwiseNatIsoData`. The trust boundary should be explicit: either the early primitive is the
book axiom data, or the objectwise theorem is checked from earlier primitives.

### Option C: introduce a lower-level invertibility notion for components

Define component invertibility using a lower-level interval or equivalence-edge package that does
not itself mention `NatIso`, then relate it to `InvertibleMorphism` after Chapter 1.

This is the cleanest route if the current `InvertibleMorphism` package remains dependent on
`NatIso` comparisons. It also aligns well with the model blueprint for maximal cores and
equivalence edges.

## Recommended first pass

### Project 1: dependency audit

Goal: draw the dependency cycle precisely.

Expected result:

- a list of declarations that `ObjectwiseNatIsoData` would need for the direct package body;
- a list of declarations that already depend on `NatIso`;
- a proposed non-circular package design.

### Project 2: projection API

Goal: make the projection from objectwise evidence to component invertibility checked.

Target declaration:

```lean
SCT.objectwiseNatIsoComponent
```

Expected result:

- either a checked projection from a checked `ObjectwiseNatIsoData` package;
- or a checked projection from a clearly documented objectwise criterion package introduced after
  the necessary Chapter 1 vocabulary.

### Project 3: constructor API

Goal: make the constructor direction clear and stable.

Target declaration:

```lean
SCT.natIsoOfObjectwise
```

This declaration is currently a direct Sigma constructor. If the package design changes, preserve
the same mathematical behavior: objectwise invertibility evidence should assemble into a natural
isomorphism.

### Project 4: downstream adapters

Goal: update the Chapter 6 proofs that use objectwise natural isomorphisms.

Expected result:

- `natIsoObjectwiseComponent` remains usable;
- `funCatPostcompFullyFaithful` has the componentwise tools it needs;
- the Fundamental Theorem project can use natural isomorphisms componentwise without unfolding
  unrelated package internals.

## Pitfalls

- Do not define `ObjectwiseNatIsoData` as `True`, `PUnit`, or strict equality of functors.
- Do not make natural isomorphisms strict equalities of natural transformations.
- Do not introduce a circular definition where `NatIso` is defined through `InvertibleMorphism` and
  `InvertibleMorphism` is defined through `NatIso`.
- Keep the distinction clear between the internal SCT package and the quasicategory model's
  bicategorical natural isomorphisms.

## Expected result

A successful project gives SCT a reliable objectwise natural-isomorphism API. This directly supports
the Fundamental Theorem, equivalence recognition, postcomposition results, and later fibration and
Rezk-equivalence arguments.
