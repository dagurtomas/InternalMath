# Fundamental Theorem internal blueprint

## Project overview

The Fundamental Theorem of category theory says that a functor is an equivalence when it is fully
faithful and essentially surjective. In SCT, essential surjectivity is represented by strong
surjectivity: a section of the induced functor on cores. This project turns the Chapter 6 theorem
package into checked internal proofs and then uses it to derive the main equivalence-recognition
results needed by later chapters.

## Project dependencies

- Depends on [Strong surjectivity](StrongSurjectivityInternalBlueprint.md) for extracting ordinary
  preimage objects and comparison isomorphisms from a strong-surjectivity section on cores.
- Depends on [Core and Axiom G](CoreAxiomGInternalBlueprint.md) for reliable core functoriality and
  core comparison data.
- Depends on [Objectwise natural isomorphism](ObjectwiseNatIsoInternalBlueprint.md) for the
  objectwise natural-isomorphism criterion used in postcomposition and equivalence arguments.
- Uses the [subcategory and full subcategory](SubcategoryFullSubcategoryInternalBlueprint.md)
  project for the application to full subcategory inclusions.
- Best treated as a capstone internal project after the dependencies above have stable APIs.

Workshop blueprint for the Chapter 6 Fundamental Theorem cluster.

Target modules:

```text
InternalMath/SCT/Spec/Chapter6/Definitions.lean
InternalMath/SCT/Spec/Chapter6/Conservativity.lean
InternalMath/SCT/Spec/Chapter6/StrongSurjectivity.lean
InternalMath/SCT/Spec/Chapter6/Retracts.lean
InternalMath/SCT/Spec/Chapter6/FundamentalTheorem.lean
```

Related modules:

```text
InternalMath/SCT/Spec/Chapter2/Cores.lean
InternalMath/SCT/Spec/Chapter3/FullSubcategories.lean
InternalMath/SCT/Spec/Chapter5/Fibrations.lean
```

## Admissions in scope

Core Chapter 6 theorem declarations:

```lean
SCT.fullyFaithfulHomEquiv
SCT.fullyFaithfulConservative
SCT.conservativeReflectsIso
SCT.conservativeOfRetract
SCT.fundamental_theorem_equiv
SCT.equivalenceFullyFaithful
SCT.equivalenceStronglySurjective
```

Applications and later Chapter 6 declarations:

```lean
SCT.fullSubcategoryEquivOfStronglySurjective
SCT.cocartesianFunctorFiberwiseEquiv
SCT.funCatPostcompFullyFaithful
```

Closely related objectwise and strong-surjectivity declarations live in separate blueprints:

```lean
SCT.objectwiseNatIsoComponent
SCT.stronglySurjectivePreimage
SCT.stronglySurjectiveBeta
```

## Mathematical target

The current SCT definitions are:

```lean
FullyFaithful C D F :=
  CatEquiv (funCat intervalCat C)
    (pullbackCat (prodCat C C) (funCat intervalCat D) (prodCat D D)
      (objectPairFunctor C D F) (arrowEndpointFunctor D))
```

and

```lean
StronglySurjective C D F :=
  Σ s : Functor (coreCat D) (coreCat C),
    NatIso (coreCat D) (coreCat D)
      (compFunctor (coreCat D) (coreCat C) (coreCat D) s (coreFunctor C D F))
      (idFunctor (coreCat D))
```

The theorem should construct:

```lean
CatEquiv C D
```

from:

```lean
ff   : FullyFaithful C D F
surj : StronglySurjective C D F
```

Informally, the inverse sends `y : D` to a chosen preimage object `x : C`. Fully faithfulness then
lifts the arrows and comparison data needed to make this object assignment functorial and to build
the unit and counit natural isomorphisms.

## Proof families

### A. Fully faithful functors and hom categories

Target declaration:

```lean
SCT.fullyFaithfulHomEquiv
```

The endpoint-pullback definition of full faithfulness should imply equivalences on fixed-endpoint
hom categories:

```text
Hom_C(x,y) ≃ Hom_D(Fx,Fy).
```

This is a key bridge from the global arrow-category pullback criterion to objectwise reasoning.

### B. Conservativity

Target declarations:

```lean
SCT.fullyFaithfulConservative
SCT.conservativeReflectsIso
SCT.conservativeOfRetract
```

These results say that fully faithful functors and suitable retracts reflect invertibility. They are
used in equivalence-recognition arguments and in later fibration criteria.

Expected proof ingredients:

- `FullyFaithful` as the endpoint-pullback equivalence;
- `Conservative` as the core-pullback square;
- invertible interval-shaped morphisms;
- core inclusions and core functoriality.

### C. Fundamental Theorem

Target declaration:

```lean
SCT.fundamental_theorem_equiv
```

The proof should build a quasi-inverse to `F` from strong-surjectivity data and use full
faithfulness to define its action on arrows. The unit and counit are natural isomorphisms assembled
from:

1. the strong-surjectivity section comparison on cores;
2. the fully faithful hom equivalences;
3. objectwise natural-isomorphism packaging.

### D. Equivalences give the hypotheses

Target declarations:

```lean
SCT.equivalenceFullyFaithful
SCT.equivalenceStronglySurjective
```

A packaged equivalence should be fully faithful and strongly surjective. The strong-surjectivity
section is induced by the inverse functor on cores:

```text
D^≃ → C^≃.
```

The beta comparison comes from the counit of the equivalence and functoriality of cores.

### E. Applications

Target declarations:

```lean
SCT.fullSubcategoryEquivOfStronglySurjective
SCT.cocartesianFunctorFiberwiseEquiv
SCT.funCatPostcompFullyFaithful
```

These should be treated after the main theorem is stable.

- A full subcategory inclusion that is strongly surjective should be an equivalence by the
  Fundamental Theorem.
- A cocartesian functor that is fiberwise an equivalence should be an equivalence after transport
  along cocartesian arrows.
- Postcomposition with a fully faithful functor should be fully faithful by applying full
  faithfulness objectwise to natural transformations.

## Suggested workshop split

### Project 1: fixed-endpoint hom equivalence

Goal: prove `fullyFaithfulHomEquiv` from the endpoint-pullback definition.

Expected result:

- a checked equivalence on `objectHomCat` fibers;
- helper lemmas relating endpoint fibers to the pullback defining `FullyFaithful`.

### Project 2: conservativity package

Goal: close the conservativity declarations.

Expected result:

- checked `fullyFaithfulConservative`;
- checked `conservativeReflectsIso`;
- checked `conservativeOfRetract`.

### Project 3: construct the Fundamental Theorem equivalence

Goal: prove `fundamental_theorem_equiv`.

Expected result:

- forward functor is the given `F`;
- backward functor comes from strong surjectivity plus fully faithful arrow lifting;
- unit and counit are packaged as `NatIso` data.

### Project 4: reverse direction for packaged equivalences

Goal: prove that equivalences are fully faithful and strongly surjective.

Expected result:

- checked `equivalenceFullyFaithful`;
- checked `equivalenceStronglySurjective`;
- existing projections `equivalenceStronglySurjectiveSection` and
  `equivalenceStronglySurjectiveSectionBeta` remain valid.

### Project 5: downstream applications

Goal: close the three application declarations after the main theorem is in place.

Expected result:

- full subcategory equivalence from strong surjectivity;
- fiberwise cocartesian equivalence criterion;
- postcomposition fully faithful.

## Pitfalls

- Do not prove the Fundamental Theorem by adding a new primitive equivalence field.
- Do not replace essential surjectivity by a strict chosen inverse on objects.
- Do not use strict equality where the SCT interface asks for `NatIso` or `CatEquiv`.
- Keep theorem-shaped declarations as internal proofs; do not move them into the model interface.
- Separate the main theorem from the later fibration application so the first useful result is not
  blocked by Chapter 5 and Chapter 7 infrastructure.

## Expected result

A successful project gives Chapter 6 a checked equivalence-recognition theorem and removes a large
cluster of theorem-shaped admissions. It also supplies downstream tools for full subcategories,
postcomposition, fibration equivalence criteria, and later universe work.
