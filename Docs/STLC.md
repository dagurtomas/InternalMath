# Simply typed lambda calculus and Curry--Howard--Lambek

This guide describes the STLC development in `InternalMath/LambdaCalculus`. It is the main complete
example in this repository: it starts from an InternalLean declaration of a type theory, builds
semantic models, and constructs the associated syntactic cartesian closed category.

The implementation is still experimental because it depends on InternalLean's generated model
interfaces and LF transport machinery. The mathematical scope is simply typed lambda calculus with
finite products and function types.

## Files

- `InternalMath/LambdaCalculus/Basic.lean` declares the type theory `LambdaCalculus`.
- `InternalMath/LambdaCalculus/Model.lean` generates `LambdaCalculusModel` and proves the
  Curry--Howard--Lambek constructions.

## Type theory declaration

`LambdaCalculus` is an intrinsic STLC presentation. Its main syntax sorts are:

- `Ctx` — contexts;
- `Ty` — simple types;
- `Tm Γ A` — typed terms of type `A` in context `Γ`;
- `Sub Γ Δ` — explicit substitutions from `Γ` to `Δ`.

The calculus includes:

- unit, binary product, and function types;
- empty context and one-variable context extension;
- identity, composition, empty, weakening, and extended substitutions;
- term reindexing along substitutions;
- product introduction/projections and lambda/application;
- definitional equality judgments `EqTm` and `EqSub`;
- β/η and congruence rules for products, unit, functions, and substitution.

Several operations are checked LF definitions rather than primitive model obligations. For example,
`weakenTm`, `substTop`, and one-variable composition `homComp` are all defined internally from
substitution structure.

## Context representability

The theory includes explicit data saying that every context can be represented by a single type:

```lean
ctxObj Γ : Ty
ctxToSingleton Γ : Sub Γ (extendCtx emptyCtx (ctxObj Γ))
ctxFromSingleton Γ : Sub (extendCtx emptyCtx (ctxObj Γ)) Γ
```

with inverse laws `ctxToFrom` and `ctxFromTo`. This is the extra democratic/contextual structure
needed to compare arbitrary STLC contexts with morphisms out of a single object in the syntactic
category.

## Forward direction: CCCs are models

`Model.lean` defines:

```lean
CCC.lambdaCalculusModel : LambdaCalculusModel
```

for any Lean category `C` with `Category C`, `CartesianMonoidalCategory C`, and `MonoidalClosed C`.
The interpretation is the usual one:

- contexts and types are objects of `C`;
- terms and substitutions are morphisms;
- context extension and product types are tensor/product objects;
- function types are internal homs;
- lambda/application use the closed monoidal adjunction.

The equality judgments are interpreted by lifted Lean equality.

## Backward direction: the syntactic CCC of a model

For any `M : LambdaCalculusModel`, `Model.lean` constructs a category whose objects are STLC types
and whose morphisms `A ⟶ B` are one-variable terms

```lean
Tm (extendCtx emptyCtx A) B
```

quotiented by definitional equality. Composition is the derived `homComp` operation. The file then
constructs:

- the category instance on `M.category`;
- terminal and binary product cones from `unitTy` and `prodTy`;
- a cartesian monoidal structure;
- internal homs from `arrowTy`;
- a `MonoidalClosed` instance.

This is the syntactic cartesian closed category associated to the STLC model.

## Curry--Howard--Lambek equivalence

For a cartesian closed category `C`, the forward model can be sent back to its syntactic category.
`Model.lean` defines the canonical functor

```lean
CCC.toSyntacticFunctor : C ⥤ (CCC.lambdaCalculusModel C).category
```

and proves it is full, faithful, and essentially surjective. The resulting equivalence is:

```lean
equivalence : C ≌ (CCC.lambdaCalculusModel C).category
```

The file also equips the comparison functors with monoidal structure using the chosen finite
products.

## Comparison for arbitrary contexts

The one-variable syntactic category is enough for the categorical CCC, but STLC terms are indexed by
arbitrary contexts. The representability fields provide quotient-level comparison data:

```lean
LambdaCalculusModel.ContextComparison
LambdaCalculusModel.contextComparison
LambdaCalculusModel.hasCurryHowardLambekComparison
```

For each context `Γ`, the comparison maps terms modulo `EqTm` to morphisms
`ctxObj Γ ⟶ A`, and substitutions modulo `EqSub` to morphisms `ctxObj Γ ⟶ ctxObj Δ`.

## Useful checks

```bash
lake build InternalMath.LambdaCalculus.Basic
lake build InternalMath.LambdaCalculus.Model
```
