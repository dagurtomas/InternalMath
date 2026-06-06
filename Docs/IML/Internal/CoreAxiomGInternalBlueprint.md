# Core and Axiom G internal blueprint

## Project overview

The core `C^≃` of a synthetic category should be the part of `C` containing all objects and only
invertible arrows. Axiom G says that cores are groupoids, that groupoids are the same kind of data
as anima, and that maps from groupoids into `C` factor through `C^≃`. This project turns the main
internal consequences of that axiom into checked declarations so later projects can reason with
cores rather than treating them as opaque objects.

## Project dependencies

- Can start after the Chapter 1 core inputs are available: terminal categories, interval shapes,
  functor categories, products, pullbacks, and the basic `NatIso`/`CatEquiv` operations.
- Does not depend on the subcategory blueprint, but it unlocks cleaner proofs in the subcategory,
  strong-surjectivity, Fundamental Theorem, and groupoid-universe projects.
- Some low-dimensional endpoint equivalences use finite shape facts about `[1]`, `[2]`, products,
  coproducts, and pullbacks. These are good subprojects if the full core universal property is too
  large for one session.

Workshop blueprint for the Chapter 2 core and Axiom G cluster.

Target module:

```text
InternalMath/SCT/Spec/Chapter2/Cores.lean
```

## Admissions in scope

The core cluster contains these admitted internal declarations:

```lean
SCT.mapAnimaCoreEquiv
SCT.funCatTargetGroupoid
SCT.intervalCoreEndpointEquiv
SCT.coreProductEquiv
SCT.corePullbackEquiv
SCT.simplex2CoreEndpointEquiv
SCT.coprodGroupoid
SCT.pullbackGroupoid
SCT.initialGroupoid
```

A first workshop pass can focus on a smaller slice, but the declarations above are the coherent
Axiom G project: they all say that cores, groupoids, and finite constructions interact in the
expected way.

## Mathematical target

Axiom G gives the groupoid/anima comparison and the core universal property. In the current SCT
interface the primitive fields and checked projections include:

```lean
GroupoidWitness
groupoidOfAnima
animaOfGroupoid
animaOfGroupoidEquiv
coreAnima
coreCat
coreIncl
coreUniversalPackage
coreLift
coreLiftBeta
coreLiftUniq
coreFunctor
coreFunctorBeta
coreOfGroupoidEquiv
```

The informal picture is:

```text
C^≃ = Map(*, C)
```

and for every groupoid `G`, a functor `G → C` factors through the inclusion

```text
C^≃ → C
```

uniquely up to natural isomorphism. When `C` is already a groupoid, the inclusion `C^≃ → C` is an
equivalence.

## Main proof families

### A. Mapping anima as the core of a functor category

The declaration

```lean
SCT.mapAnimaCoreEquiv
```

should compare `Map(C,D)` with the core of `Fun(C,D)`:

```text
animaCat (Map(C,D)) ≃ Fun(C,D)^≃.
```

This is the most central result in the cluster. It connects the primitive mapping-anima operation
from Axiom A with the Chapter 2 core API from Axiom G.

Useful ingredients:

- `coreUniversalPackage`;
- currying and uncurrying for functor categories;
- `coreOfGroupoidEquiv`;
- `animaOfGroupoidEquiv` and `groupoid_anima_equiv`.

### B. Functor categories with groupoid target

The declaration

```lean
SCT.funCatTargetGroupoid
```

should say that if `D` is a groupoid, then `Fun(C,D)` is a groupoid. The intended proof uses the
interval characterization of groupoids and functor-category exponential laws:

```text
Fun([1], Fun(C,D)) ≃ Fun(C, Fun([1],D)).
```

Then use the groupoid witness for `D` pointwise.

### C. Cores commute with finite constructions

The declarations

```lean
SCT.coreProductEquiv
SCT.corePullbackEquiv
SCT.coprodGroupoid
SCT.pullbackGroupoid
SCT.initialGroupoid
```

express that groupoidal structure and cores are stable under the finite constructions needed later.
The product and pullback comparisons should be equivalences such as:

```text
(C × D)^≃ ≃ C^≃ × D^≃
(C ×_E D)^≃ ≃ C^≃ ×_{E^≃} D^≃.
```

These comparisons feed object and morphism collection arguments, because those collections live in
cores and mapping anima.

### D. Low-dimensional endpoint cores

The declarations

```lean
SCT.intervalCoreEndpointEquiv
SCT.simplex2CoreEndpointEquiv
```

identify the cores of the walking interval and walking composable-pair shape with finite discrete
categories:

```text
[1]^≃ ≃ {*} ⊔ {*}
[2]^≃ ≃ {*} ⊔ {*} ⊔ {*}
```

These are useful for endpoint bookkeeping in Chapter 3 and Chapter 6.

## Suggested workshop split

### Project 1: map-anima/core comparison plan

Goal: isolate the exact functor-category and currying facts needed for `mapAnimaCoreEquiv`.

Expected result:

- a short internal proof outline in comments or a local note;
- named helper declarations for the forward and backward functors if the proof is too large;
- no new primitive fields for the theorem itself.

### Project 2: groupoid target functor categories

Goal: prove `funCatTargetGroupoid` from the interval characterization of groupoids.

Expected result:

- a checked `funCatTargetGroupoid`;
- helper definitions for the comparison
  `Fun([1], Fun(C,D)) ≃ Fun(C, Fun([1],D))` if needed.

### Project 3: finite core equivalences

Goal: close `intervalCoreEndpointEquiv` and `simplex2CoreEndpointEquiv`.

Expected result:

- finite endpoint equivalences usable by Chapter 3 and Chapter 6;
- no reliance on strict equality between categories that are only equivalent.

### Project 4: stability of groupoids and cores under finite limits/colimits

Goal: close the product, coproduct, pullback, and initial groupoid declarations.

Expected result:

- checked groupoid witnesses for the basic finite constructions;
- checked core comparison equivalences for products and pullbacks.

## Pitfalls

- Do not replace core universal properties by strict equalities of categories.
- Do not make `mapAnimaCoreEquiv` a new primitive model obligation; it is theorem-shaped internal
  debt.
- Keep groupoid/anima comparisons explicit. A category equivalent to an anima becomes an anima by
  `equiv_to_anima_is_anima`, but the equivalence data still matters.
- When a construction is only unique up to equivalence, package the result as `CatEquiv` or
  `NatIso`, not as definitional equality.

## Expected result

A successful project removes a large part of the Chapter 2 core admission cluster and gives later
internal projects a reliable API for moving between categories, their cores, groupoids, and mapping
anima.
