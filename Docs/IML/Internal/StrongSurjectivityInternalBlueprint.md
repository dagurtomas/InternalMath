# Strong-surjectivity internal blueprint

## Project overview

Strong surjectivity says that every object of the target category is represented, up to equivalence,
by an object coming from the source category. This project turns that abstract section of cores into
ordinary data: given `y` in `D`, choose an object `x` in `C` and build the comparison `F x ≅ y`.

## Project dependencies

- The required core API is already present in the SCT specification: `coreLiftFromGroupoid`,
  `coreLiftFromGroupoidBeta`, `coreFunctor`, `coreFunctorBeta`, and the basic `NatIso` operations.
- Does not require the Fundamental Theorem. This project supplies object-level data that the
  Fundamental Theorem blueprint later uses.
- Pairs well with the Core/Axiom G blueprint, but the two admissions in this file are a focused
  projection exercise from the existing strong-surjectivity package.

Workshop blueprint for `InternalMath/SCT/Spec/Chapter6/StrongSurjectivity.lean`.

Scope: close the two internal admissions that extract ordinary object-level data from the internal
Definition 6.3.1 representation of strong surjectivity.

Target module:

```text
InternalMath/SCT/Spec/Chapter6/StrongSurjectivity.lean
```

Admissions in that module:

```lean
SCT.stronglySurjectivePreimage
SCT.stronglySurjectiveBeta
```

Expected result of a successful project: these two declarations become checked internal definitions
and disappear from the admitted declaration list.

## Mathematical target

Definition:

```lean
syntax_abbrev StronglySurjective (C : SCat) (D : SCat) (F : Functor C D) :=
  Σ s : Functor (coreCat D) (coreCat C),
    NatIso (coreCat D) (coreCat D)
      (compFunctor (coreCat D) (coreCat C) (coreCat D) s (coreFunctor C D F))
      (idFunctor (coreCat D))
```

So strong surjectivity gives a section of the induced functor on cores,

```text
s : D^≃ → C^≃,
s ≫ F^≃ ≅ id_{D^≃}.
```

Given an ordinary object `y : * → D`, first lift it through the core inclusion of `D`:

```text
ŷ : * → D^≃,
ŷ ≫ coreIncl D ≅ y.
```

Then apply the section and include back into `C`:

```text
x := ŷ ≫ s ≫ coreIncl C : * → C.
```

The beta comparison

```text
F x ≅ y
```

comes from three pieces:

1. `coreFunctorBeta C D F`, relating `coreIncl C ≫ F` to `F^≃ ≫ coreIncl D`;
2. the strong-surjectivity section comparison `s ≫ F^≃ ≅ id`;
3. the core-lift beta comparison `ŷ ≫ coreIncl D ≅ y`.

## Existing ingredients

Already available from earlier modules:

- `terminalCat := animaCat terminalAnima`;
- `groupoidOfAnima terminalAnima : GroupoidWitness terminalCat`;
- `coreLiftFromGroupoid`;
- `coreLiftFromGroupoidBeta`;
- `coreFunctor`;
- `coreFunctorBeta`;
- `compFunctor`, `assocFunctor`, `assocFunctorInv`, `leftUnitor`, `rightUnitor`;
- `preWhiskerNatIso`, `postWhiskerNatIso`, `compNatIso`, `invNatIso`.

The projections

```lean
stronglySurjectiveSection
stronglySurjectiveSectionBeta
```

live in `Chapter6/FundamentalTheorem.lean`.  For this project, either use `fst surj` and `snd surj`
directly, or first move those two projection definitions into
`Chapter6/StrongSurjectivity.lean` as a no-semantic-change preparatory edit.

## Recommended helper definitions

Add these before the two target admissions, unless the final proof is short enough without them.

### Terminal groupoid witness

```lean
lf_def terminalGroupoid : GroupoidWitness terminalCat :=
  groupoidOfAnima terminalAnima
```

This is just a readable alias.

### Core lift of an ordinary object

```lean
lf_def objectCoreLift : (D : SCat) ⇒ Obj D ⇒ Obj (coreCat D) :=
  fun D y => coreLiftFromGroupoid terminalCat D terminalGroupoid y
```

Beta:

```lean
lf_def objectCoreLiftBeta : (D : SCat) ⇒ (y : Obj D) ⇒
    NatIso terminalCat D
      (compFunctor terminalCat (coreCat D) D (objectCoreLift D y) (coreIncl D)) y :=
  fun D y => coreLiftFromGroupoidBeta terminalCat D terminalGroupoid y
```

These names are optional, but they make the main proof much clearer.

### Core-level preimage

```lean
lf_def stronglySurjectivePreimageCore :
    (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
    StronglySurjective C D F ⇒ Obj D ⇒ Obj (coreCat C) :=
  fun C D F surj y =>
    compFunctor terminalCat (coreCat D) (coreCat C) (objectCoreLift D y) (fst surj)
```

Then the desired preimage is its composite with `coreIncl C`.

## Definition of `stronglySurjectivePreimage`

Expected checked body:

```lean
def stronglySurjectivePreimage (C : SCat) (D : SCat) (F : Functor C D)
    (surj : StronglySurjective C D F) (y : Obj D) : Obj C :=
  compFunctor terminalCat (coreCat C) C
    (stronglySurjectivePreimageCore C D F surj y) (coreIncl C)
```

Without the helper:

```lean
compFunctor terminalCat (coreCat C) C
  (compFunctor terminalCat (coreCat D) (coreCat C)
    (coreLiftFromGroupoid terminalCat D (groupoidOfAnima terminalAnima) y)
    (fst surj))
  (coreIncl C)
```

This should be straightforward.

## Proof plan for `stronglySurjectiveBeta`

Goal:

```lean
NatIso terminalCat D
  (compFunctor terminalCat C D (stronglySurjectivePreimage C D F surj y) F) y
```

Let:

```text
ŷ := objectCoreLift D y
s := fst surj
η := snd surj : s ≫ coreFunctor C D F ≅ id
```

The composite in the source is:

```text
((ŷ ≫ s) ≫ coreIncl C) ≫ F.
```

Build a chain of natural isomorphisms:

```text
((ŷ ≫ s) ≫ coreIncl C) ≫ F
  ≅ (ŷ ≫ s) ≫ (coreIncl C ≫ F)                    -- associativity
  ≅ (ŷ ≫ s) ≫ (coreFunctor F ≫ coreIncl D)         -- inverse of coreFunctorBeta
  ≅ (ŷ ≫ (s ≫ coreFunctor F)) ≫ coreIncl D         -- associativity
  ≅ (ŷ ≫ id_{D^≃}) ≫ coreIncl D                    -- whisker η
  ≅ ŷ ≫ coreIncl D                                 -- unitors
  ≅ y.                                             -- objectCoreLiftBeta
```

The orientation of `coreFunctorBeta` is:

```lean
coreFunctorBeta C D F :
  NatIso (coreCat C) D
    (compFunctor (coreCat C) (coreCat D) D (coreFunctor C D F) (coreIncl D))
    (compFunctor (coreCat C) C D (coreIncl C) F)
```

So in the chain above, the second step uses `invNatIso` of a prewhiskered `coreFunctorBeta`.

## Suggested Lean construction strategy

Do not try to write the whole proof as one giant term on the first pass.  Introduce named internal
helper definitions for the main chain steps.  A readable sequence is:

1. `stronglySurjectiveBetaAssoc₁`:
   reassociate `((ŷ ≫ s) ≫ coreIncl C) ≫ F` to `(ŷ ≫ s) ≫ (coreIncl C ≫ F)`.
2. `stronglySurjectiveBetaCoreFunctor`:
   replace `coreIncl C ≫ F` by `coreFunctor C D F ≫ coreIncl D` using `coreFunctorBeta` in the
   inverse direction, prewhiskered by `ŷ ≫ s`.
3. `stronglySurjectiveBetaAssoc₂`:
   reassociate to expose `s ≫ coreFunctor C D F`.
4. `stronglySurjectiveBetaSection`:
   use `snd surj`, prewhiskered by `ŷ` and postwhiskered by `coreIncl D`.
5. `stronglySurjectiveBetaUnit`:
   simplify `(ŷ ≫ id) ≫ coreIncl D` to `ŷ ≫ coreIncl D` using unitors and associators.
6. compose with `objectCoreLiftBeta D y`.

Each helper should have a docstring explaining the chain step.  This makes the final
`stronglySurjectiveBeta` a `compNatIso` chain rather than an unreadable nested term.

## Possible preparatory refactor

Move these definitions from `Chapter6/FundamentalTheorem.lean` to
`Chapter6/StrongSurjectivity.lean`:

```lean
stronglySurjectiveSection
stronglySurjectiveSectionBeta
```

This is a clean move with no semantic change. It lets the proof use named projections rather than
`fst surj` and `snd surj`, and it makes the module boundary match the subject matter.

## Pitfalls

- Do not reinterpret strong surjectivity as a mere Lean-level surjection on object terms. The
  definition is a section on cores.
- Do not use strict equality for the beta comparison. The goal is a `NatIso`.
- Do not bypass the core inclusion. The chosen preimage object should be obtained by applying the
  section on cores and then including into `C`.
- Do not add a new primitive projection field for this theorem. The data is already present in the
  definition of `StronglySurjective`.

## Expected result

`SCT.stronglySurjectivePreimage` and `SCT.stronglySurjectiveBeta` should be proved rather than
admitted.
