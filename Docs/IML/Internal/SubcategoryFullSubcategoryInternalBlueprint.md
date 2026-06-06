# Subcategory and full subcategory internal blueprint

Workshop blueprint for the Chapter 3 subcategory cluster.

Scope: workshop project on subcategory witnesses, the collection of all morphisms, full
subcategories, and the API for object and morphism collection side structures.

Target modules:

```text
InternalMath/SCT/Spec/Chapter3/Subobjects.lean
InternalMath/SCT/Spec/Chapter3/Subcategories.lean
InternalMath/SCT/Spec/Chapter3/FullSubcategories.lean
InternalMath/SCT/Spec/Chapter3/FullSubcategoryLifts.lean
```

Related downstream module:

```text
InternalMath/SCT/Spec/Chapter1/IsoRezk.lean
```

This is a strong workshop target because it unlocks `Iso(C)`, Rezk adapters, inverting functor
categories, localization consequences, and several Chapter 6 theorems.

## Admissions in scope

### `Chapter3/Subobjects.lean`

```lean
SCT.idSubcategoryWitness
SCT.initialSubcategoryWitness
SCT.subcategoryWitnessEmbedding
```

### `Chapter3/Subcategories.lean`

```lean
SCT.all_morphisms_contains_identities
SCT.all_morphisms_closed
SCT.subcategoryInclWitness
```

### `Chapter3/FullSubcategories.lean`

```lean
SCT.fullSubcategoryCoreEquiv
SCT.fullSubcategoryAllObjectsEquiv
```

### `Chapter3/FullSubcategoryLifts.lean`

```lean
SCT.fullSubcategoryInclLands
SCT.landsInObjectCollectionPreservesFull
```

The cluster has ten admissions. Some are proof obligations; several depend on side structure
packages whose admitted bodies do not expose constructors.

## Reading `Σ` packages

InternalLean uses `Σ` for dependent pair packages. A term of

```lean
Σ x : A, B x
```

contains two pieces of data:

1. a first component `x : A`;
2. a second component of type `B x`, which may mention the first component.

The projections are `fst p` and `snd p`. Nested `Σ` packages act like records with named fields:

```lean
Σ S : SCat,
  Σ i : Functor S C,
    PreservesMorphismCollection S C W i
```

means: choose a category `S`, then choose a functor `i : S → C`, then give evidence that `i`
preserves `W`. The third field may mention both earlier choices. In projection code,
`fst p` is `S`, `fst (snd p)` is `i`, and `snd (snd p)` is the preservation evidence.

The blueprint uses `Σ` this way to spell out the data that a definition or axiom package should
provide. It is often clearer than introducing a Lean structure while the InternalLean interface is
being designed.

## Existing definitions

### Subcategory witness

```lean
syntax_abbrev SubcategoryWitness (A : SCat) (C : SCat) (i : Functor A C) :=
  Σ arrow_emb : SubcategoryArrowEmbedding A C i, SubcategoryPullbackCriterion A C i
```

where:

```lean
SubcategoryArrowEmbedding A C i :=
  Embedding (mapCat intervalCat A) (mapCat intervalCat C)
    (mapPostcompFunctor intervalCat A C i)

SubcategoryPullbackCriterion A C i :=
  (X : SCat) → SubcategoryPullbackSquare A C i X
```

This matches the book's replete subcategory criterion closely enough to keep as a real definition.

### Morphism and object collections

```lean
MorphismCollection C := AnimaSubobject (morphismAnima C)
ObjectCollection C := AnimaSubobject (coreAnima C)
```

This matches the book's formulation: collections are subobjects of the relevant anima.

### Side structure packages

These Chapter 3 notions are admitted `syntax_def` packages:

```lean
LandsInObjectCollection
containsIdentities
closedUnderComposition
PreservesMorphismCollection
```

Their admitted bodies do not provide checked projections or constructors for obvious cases such as
"the total morphism collection contains identities".

## Recommended project phases

## Phase 0: module cleanup before proof work

Move the three `SubcategoryWitness` theorem admissions out of `Subobjects.lean` only if a smaller
module would help. A possible target is:

```text
Chapter3/SubcategoryWitnesses.lean
```

Leaving them in `Subobjects.lean` is also fine. The benefit of a move is that `Subobjects.lean`
would contain only definitions of arrow action, mapping anima, and collections.

If a move is done, keep it separate from proof work.

## Phase 1: expose the factorization data

This is the most important design step. The goal is to replace the admitted package bodies by
checked `syntax_def` packages that expose the factorization data used in the book.

### `LandsInObjectCollection`

Target meaning:

```text
F : D → C lands in P ⊆ C^≃
```

should mean that the induced map on cores factors through the inclusion of the object collection:

```text
D^≃ --F^≃--> C^≃
       ↑
       P
```

Possible definition shape:

```lean
syntax_def LandsInObjectCollection (D : SCat) (C : SCat)
    (P : ObjectCollection C) (F : Functor D C) : Type u :=
  Σ L : Functor (coreCat D) (objectCollectionCat C P),
    NatIso (coreCat D) (coreCat C)
      (compFunctor (coreCat D) (objectCollectionCat C P) (coreCat C)
        L (objectCollectionIncl C P))
      (coreFunctor D C F)
```

This records membership in the object collection as factorization data.

### `PreservesMorphismCollection`

Target meaning:

```text
F : D → C preserves W ⊆ Map([1],C)
```

should mean that the arrow action map induced by `F`

```text
Map([1],D) → Map([1],C)
```

factors through `W`.

Possible definition shape:

```lean
syntax_def PreservesMorphismCollection (D : SCat) (C : SCat)
    (W : MorphismCollection C) (F : Functor D C) : Type u :=
  Σ L : Functor (coreCat (funCat intervalCat D)) (morphismCollectionCat C W),
    NatIso (coreCat (funCat intervalCat D)) (coreCat (funCat intervalCat C))
      (compFunctor (coreCat (funCat intervalCat D)) (morphismCollectionCat C W)
        (coreCat (funCat intervalCat C)) L (morphismCollectionIncl C W))
      (mapPostcompFunctor intervalCat D C F)
```

This gives a direct constructor for preservation by total morphism collections and for preservation
from endpoint data.

### `containsIdentities`

Target meaning: the identity arrow map factors through `W`.

The definition needs an identity arrow map

```text
C^≃ → Map([1], C)
```

One candidate is the core lift of the identity arrow functor:

```text
coreCat C --coreIncl C--> C --groupoidConstArrowFunctor C--> Fun([1],C)
```

then lift to the core of the arrow category:

```text
coreCat C → coreCat (Fun([1],C)).
```

The factorization through `morphismCollectionIncl C W` is the desired evidence.

### `closedUnderComposition`

Target meaning: composable pairs of arrows in `W` have composite in `W`.

This is the hardest of these side structures to define cleanly. It should be a factorization
statement for
the composite arrow map out of the category of pairs of composable arrows selected by `W`. A
plausible shape is:

1. build a category of composable selected arrows by pulling back two copies of `W` over endpoints;
2. map it to `composableMorphismsCat C`;
3. compose using `composeComposableMorphism` or the Segal composite;
4. require the resulting arrow map to factor through `W`.

This may deserve its own small design session. Do not fake it with an unstructured inhabitant.

## Phase 2: repair the Axiom H package

Package:

```lean
lf_opaque subcategoryPackage (C : SCat) (W : MorphismCollection C)
    (ids : containsIdentities C W) (comp : closedUnderComposition C W) :
  Σ S : SCat,
    Σ i : Functor S C,
      Σ pres : PreservesMorphismCollection S C W i,
        ... universal lift data ...
```

It does not directly store that `i : S → C` satisfies the book's `SubcategoryWitness` criterion.
The internal admission

```lean
subcategoryInclWitness
```

therefore has no obvious projection source.

Recommended repair matching Axiom H:

```lean
lf_opaque subcategoryPackage ... :
  Σ S : SCat,
    Σ i : Functor S C,
      Σ subcat : SubcategoryWitness S C i,
        Σ pres : PreservesMorphismCollection S C W i,
          ... universal lift data ...
```

Then:

```lean
subcategoryInclWitness := projection from subcategoryPackage
subcategoryInclPreserves := later projection index adjusted by one `snd`
subcategoryLift := later projection index adjusted by one `snd`
```

This changes the model interface, but it is justified: Axiom H constructs a subcategory, not merely a
category with a universal lift. The quasicategory model will eventually have to provide this
witness anyway.

Alternative route: prove `SubcategoryWitness S C i` from the universal lift package. This may be
possible but looks substantially harder and less close to the way the book states the construction.

## Phase 3: close the collection of all morphisms admissions

Targets:

```lean
all_morphisms_contains_identities
all_morphisms_closed
```

After Phase 1, these should reduce to direct constructors:

- `allMorphisms C` is the total subobject of `morphismAnima C`;
- every map into `morphismAnima C` factors through the identity inclusion of the total subobject;
- identity arrows and composites therefore land in `allMorphisms C`.

Until `closedUnderComposition` has a checked package body, these cannot be proved without adding
assumptions. Do not add ad hoc opaque fields just to close them unless the project explicitly
decides that these examples are part of the book's axiom data.

## Phase 4: close full subcategory landing and preservation

Targets:

```lean
fullSubcategoryInclLands
landsInObjectCollectionPreservesFull
```

### `landsInObjectCollectionPreservesFull`

Given:

```lean
h : LandsInObjectCollection D C P F
```

and an arrow `f : [1] → D`, the image arrow `F f : [1] → C` has source and target in `P` because
`F` lands in `P` on objects. Use

```lean
fullSubcategoryMorphismMemberIntro
```

to show the image arrow belongs to `fullSubcategoryMorphismCollection C P`. This constructs
`PreservesMorphismCollection D C (fullSubcategoryMorphismCollection C P) F`.

This proof becomes formal only after `LandsInObjectCollection` and `PreservesMorphismCollection`
have checked package bodies exposing factorization data.

### `fullSubcategoryInclLands`

The full subcategory inclusion preserves the morphism collection restricted by endpoints by
construction:

```lean
subcategoryInclPreserves
```

For an object of the full subcategory, apply preservation to its identity arrow. Then use

```lean
fullSubcategoryMorphismMemberElim
```

to recover endpoint membership in `P`. The endpoint of the identity arrow is the original object, by
compatibility of identity source and target. This gives `LandsInObjectCollection` for the inclusion.

This proof requires coherence bookkeeping but is suitable for an agent after Phase 1.

## Phase 5: close `subcategoryWitnessEmbedding`

Target:

```lean
subcategoryWitnessEmbedding : SubcategoryWitness A C i → Embedding A C i
```

This is Lemma 3.1.5 in the book.

Proof idea:

- `SubcategoryWitness` gives a pullback criterion for every test category `X`.
- Use the criterion with a suitable test shape to identify objects and arrows of `A` over `C`.
- Combine with the embedding for the arrow map to show that the diagonal comparison
  `A → A ×_C A` is an equivalence.

This is likely the hardest theorem in the subcategory cluster. It may require auxiliary lemmas
connecting:

- `mapCat terminalCat A` with `coreCat A` or objects of `A`;
- arrow embeddings with equality or equivalence of parallel objects in `A ×_C A`;
- Rezk reconstruction of objects and arrows.

Do not block the earlier phases on this theorem. Closing it matters because
`isoProjectionEmbedding` in `Chapter1/IsoRezk.lean` depends on it.

## Phase 6: identity and initial subcategories

Targets:

```lean
idSubcategoryWitness
initialSubcategoryWitness
```

### Identity functor

For `idFunctor C`, the arrow action map is equivalent to the identity on `mapCat intervalCat C`, so
its embedding witness should be `identityEmbedding`. The pullback criterion should reduce to the
identity pullback square for the square comparing `arrowActionMapFunctor` with itself.

Expected ingredients:

- unitors for composition with `idFunctor`;
- `identityEmbedding`;
- pullback uniqueness/equivalence packaging.

This requires coherence bookkeeping but is conceptually straightforward.

### Initial inclusion

For `initialElim C : initialCat → C`, use strict initiality and uniqueness out of `initialCat`.
The relevant mapping categories out of and into `initialCat` should be contractible/initial in the
right way. This may need helper lemmas about functor categories with initial source and about
mapping anima of the initial category.

This target has lower priority than the full subcategory and all morphism collection work.

## Phase 7: full subcategory core comparison

Targets:

```lean
fullSubcategoryCoreEquiv
fullSubcategoryAllObjectsEquiv
```

### `fullSubcategoryCoreEquiv`

The core of a full subcategory should be exactly its object collection:

```text
(fullSubcategory C P)^≃ ≃ P.
```

Proof plan:

1. Map `(fullSubcategory C P)^≃` to `P` using `fullSubcategoryInclLands` restricted to the core.
2. Map `P` to `(fullSubcategory C P)^≃` using the full subcategory lift for the composite
   `objectCollectionCat C P → coreCat C → C`.
3. Use the full subcategory lift β/uniqueness and the core universal property to build unit and
   counit.

Likely dependencies:

- `fullSubcategoryInclLands`;
- `fullSubcategoryLift`, `fullSubcategoryLiftBeta`, `fullSubcategoryLiftUniq`;
- `coreLift`/`coreLiftUniq`;
- `subcategoryWitnessEmbedding` or an equivalent embedding theorem for full subcategories.

### `fullSubcategoryAllObjectsEquiv`

If `P ≃ C^≃`, then the full subcategory on `P` should be equivalent to `C`.

Possible proof routes:

1. Use `fullSubcategoryCoreEquiv` plus the hypothesis `P ≃ C^≃` to show the inclusion is strongly
   surjective, then apply the Fundamental Theorem after it is proved.
2. Use the full subcategory universal property directly to construct inverse data, avoiding the
   full Chapter 6 theorem.

This should come after `fullSubcategoryCoreEquiv`. It is probably not an opening workshop target.

## Suggested workshop deliverables

### Minimum useful deliverable

- Decide and document definitions of `LandsInObjectCollection` and
  `PreservesMorphismCollection` that match the book's factorization statements.
- Move or add projection helpers so future proofs can use the factorization data.
- Keep model obligations at zero temporary fields for admitted definitions.

### First proof deliverable

- Extend `subcategoryPackage` so `subcategoryInclWitness` is a projection.
- Close `subcategoryInclWitness`.
- Adjust downstream projection paths for `subcategoryInclPreserves`, `subcategoryLift`, β, and
  uniqueness.

### Second proof deliverable

- Close `all_morphisms_contains_identities` and `all_morphisms_closed`, assuming Phase 1 definitions.

### Third proof deliverable

- Close `landsInObjectCollectionPreservesFull` and `fullSubcategoryInclLands`.

### Later deliverable

- Close `fullSubcategoryCoreEquiv`.
- Attempt `subcategoryWitnessEmbedding`.

## Dependency and priority table

| Declaration | Priority | Main blocker | Suggested action |
| --- | --- | --- | --- |
| `subcategoryInclWitness` | very high | not projected by `subcategoryPackage` | add `SubcategoryWitness` to Axiom H package |
| `all_morphisms_contains_identities` | high | admitted `containsIdentities` package | define identity factorization structure |
| `all_morphisms_closed` | high | admitted `closedUnderComposition` package | define composition factorization structure |
| `landsInObjectCollectionPreservesFull` | high | landing and preservation packages | expose factorization data |
| `fullSubcategoryInclLands` | high | landing and preservation packages, plus coherence for identity arrows | prove after landing/preservation refactor |
| `fullSubcategoryCoreEquiv` | medium/high | needs full subcategory landing and core calculus | later theorem |
| `fullSubcategoryAllObjectsEquiv` | medium | likely needs Chapter 6 or direct inverse construction | later theorem |
| `subcategoryWitnessEmbedding` | high but hard | Lemma 3.1.5 proof infrastructure | separate theorem project |
| `idSubcategoryWitness` | medium | coherence | after witness helpers |
| `initialSubcategoryWitness` | lower | initial and functor category lemmas | later |

## Things to avoid

- Do not close side structure goals with arbitrary primitive inhabitants.
- Do not turn every theorem in this cluster into a new `lf_opaque` field. Add axiom data only when
  it is genuinely part of Axiom H or the full subcategory construction.
- Do not define full subcategories as strict equalities on objects. The object collection is a
  subobject of the core, not a Lean predicate on raw terms.
- Do not use ordinary category theory arguments where the SCT statement is about mapping anima or
  cores.
- Do not combine the representation refactor with large theorem proofs in one commit.

## Expected result

A completed tranche should remove the named admissions or expose clearer package data. If the
generated model obligations change, the new field should be tied to a specific axiom or construction
from the book.
