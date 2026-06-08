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
- The package design resolves the circularity hazard by keeping early natural-isomorphism evidence
  as an abstract `ObjectwiseNatIsoData` package in the prelude, defining
  `NatIso F G := Σ α : NatTrans F G, ObjectwiseNatIsoData F G α`, and adding the componentwise
  invertibility projection only later, after interval-shaped invertible morphisms are available.
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

Mathematically, a natural isomorphism is a natural transformation whose component arrow is
invertible at every object. The package exists so later proofs can move back and forth between a
global `NatIso` and its componentwise invertibility facts.

The difficulty is import and declaration order: this expression mentions declarations from Chapter
1, while `NatIso` is introduced in the prelude before those declarations are in scope. The chosen
organization breaks the cycle by making `ObjectwiseNatIsoData` an early abstract package and making
Chapter 6 responsible for the theorem-shaped projection from that package to componentwise
`InvertibleMorphism` evidence.

## Chosen non-circular design

The current specification uses the following organization.

1. `NatTrans` is primitive early vocabulary.
2. `ObjectwiseNatIsoData F G α` is an admitted `syntax_def` package in the prelude.  It is abstract
   objectwise natural-isomorphism evidence, not a vacuous package and not a model-provider field.
3. `NatIso F G` is the Sigma package

   ```lean
   Σ natIsoTrans : NatTrans F G, ObjectwiseNatIsoData F G natIsoTrans
   ```

   so the underlying natural transformation and objectwise evidence are available immediately.
4. Chapter 1 can define interval-shaped invertible morphisms using `NatIso` comparisons without
   referring back to the componentwise criterion.
5. Chapter 6 adds the theorem-shaped projection

   ```lean
   objectwiseNatIsoComponent ... :
     InvertibleMorphism C (natTransComponent A C F G α x)
   ```

   after `natTransComponent` and `InvertibleMorphism` are both in scope.
6. The constructor direction `natIsoOfObjectwise` is checked as the Sigma constructor, and the
   projection from a `NatIso` to its objectwise evidence is checked as `snd`.

This is the intended route around the circularity hazard.  A direct checked definition of
`ObjectwiseNatIsoData` as

```lean
(x : Obj A) → InvertibleMorphism C (natTransComponent A C F G α x)
```

would mention declarations that themselves depend on `NatIso`.  The direct package can only replace
the abstract package after component invertibility is expressed through a lower-level notion that
does not depend on `NatIso`, such as an equivalence-edge or interval-invertibility predicate.

## Recommended work

### Project 1: projection API

Goal: make the projection from objectwise evidence to component invertibility checked.

Target declaration:

```lean
SCT.objectwiseNatIsoComponent
```

Expected result:

- a checked proof of the Chapter 6 projection from the abstract `ObjectwiseNatIsoData` package to
  componentwise `InvertibleMorphism` evidence; or
- a replacement of the abstract package by a lower-level non-circular package, followed by a checked
  projection to `InvertibleMorphism`.

### Project 2: constructor API

Goal: make the constructor direction clear and stable.

Target declaration:

```lean
SCT.natIsoOfObjectwise
```

This declaration is a direct Sigma constructor in the implemented design. If the package design
changes, preserve the same mathematical behavior: objectwise invertibility evidence should assemble
into a natural isomorphism.

### Project 3: downstream adapters

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
