# Subcategory and full-subcategory internal blueprint

Status: detailed workshop blueprint for the Chapter 3 subcategory cluster, 2026-05-31.

Scope: high-value internal SCT project around subcategory witnesses, all-morphism collections, full
subcategories, and the object/morphism collection side-structure API.

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

This is probably the best high-value internal workshop target because it unlocks `Iso(C)`, Rezk
adapters, inverting-functor categories, localization consequences, and several Chapter 6 theorems.

## Current admissions in scope

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

There are ten admissions in the immediate cluster.  Some are proof obligations; several are blocked
by representation because the current side structures are primitive sorts with no constructors.

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

This matches the book's replete-subcategory criterion closely enough to keep as a real definition.

### Morphism and object collections

```lean
MorphismCollection C := AnimaSubobject (morphismAnima C)
ObjectCollection C := AnimaSubobject (coreAnima C)
```

This is a good source-facing representation: collections are subobjects of the relevant anima.

### Current blocked side structures

These are now admitted `syntax_def` packages rather than primitive side sorts:

```lean
LandsInObjectCollection
containsIdentities
closedUnderComposition
PreservesMorphismCollection
```

The remaining issue is that their bodies are still admitted, so there are no checked projections or
constructors for obvious cases such as "the total morphism collection contains identities".

## Recommended project phases

## Phase 0: module cleanup before proof work

Move the three `SubcategoryWitness` theorem admissions out of `Subobjects.lean` into a more focused
module if desired.  Good options:

```text
Chapter3/SubcategoryWitnesses.lean
```

or keep them in `Subobjects.lean` for now and avoid churn.  This is optional.  The main benefit is
making `Subobjects.lean` contain only definitions of arrow action, mapping anima, and collections.

If a move is done, it should be a no-semantic-change commit checked by:

```bash
lake build InternalMath.SCT.Spec
```

## Phase 1: expose the factorization data

This is the highest-value design step.  The goal is to replace the admitted package bodies by
checked `syntax_def` packages that expose the factorization data used in the book.

### `LandsInObjectCollection`

Target meaning:

```text
F : D → C lands in P ⊆ C^≃
```

should mean that the induced map on cores factors through the object-collection inclusion:

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

This would make object-collection membership actual factorization data.

### `PreservesMorphismCollection`

Target meaning:

```text
F : D → C preserves W ⊆ Map([1],C)
```

should mean that the arrow-action map induced by `F`

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

Target meaning: the identity-arrow map factors through `W`.

The definition needs an identity-arrow map

```text
C^≃ → Map([1], C)
```

One candidate is the core lift of the identity-arrow functor:

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

This is the hardest side structure to define cleanly.  It should be a factorization statement for
the composite-arrow map out of the category of composable `W`-pairs.  A plausible shape is:

1. build a category of composable selected arrows by pulling back two copies of `W` over endpoints;
2. map it to `composableMorphismsCat C`;
3. compose using `composeComposableMorphism` or the Segal composite;
4. require the resulting arrow map to factor through `W`.

This may deserve its own small design session.  Do not fake it with an unstructured inhabitant.

## Phase 2: repair the Axiom H package

Current package:

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

Recommended source-faithful repair:

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
category with a universal lift.  The quasicategory model will eventually have to provide this
witness anyway.

Alternative route: prove `SubcategoryWitness S C i` from the universal lift package.  This may be
possible but looks substantially harder and less faithful to the way the book states the
construction.

## Phase 3: close the total-morphism collection admissions

Targets:

```lean
all_morphisms_contains_identities
all_morphisms_closed
```

After Phase 1, these should be easy:

- `allMorphisms C` is the total subobject of `morphismAnima C`;
- every map into `morphismAnima C` factors through the identity inclusion of the total subobject;
- identity arrows and composites therefore land in `allMorphisms C`.

While `closedUnderComposition` remains an admitted package, these cannot honestly be proved.  Do
not add ad hoc opaque fields just to close them unless the project explicitly decides that these
examples are part of source axiom data.

## Phase 4: close full-subcategory landing and preservation

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
`F` lands in `P` on objects.  Use

```lean
fullSubcategoryMorphismMemberIntro
```

to show the image arrow belongs to `fullSubcategoryMorphismCollection C P`.  This constructs
`PreservesMorphismCollection D C (fullSubcategoryMorphismCollection C P) F`.

This proof becomes formal only after `LandsInObjectCollection` and `PreservesMorphismCollection`
have checked package bodies exposing factorization data.

### `fullSubcategoryInclLands`

The full-subcategory inclusion preserves the endpoint-restricted morphism collection by construction:

```lean
subcategoryInclPreserves
```

For an object of the full subcategory, apply preservation to its identity arrow.  Then use

```lean
fullSubcategoryMorphismMemberElim
```

to recover endpoint membership in `P`.  The endpoint of the identity arrow is the original object, by
identity-source/target compatibility.  This gives `LandsInObjectCollection` for the inclusion.

This proof is coherence-heavy but agent-friendly after Phase 1.

## Phase 5: close `subcategoryWitnessEmbedding`

Target:

```lean
subcategoryWitnessEmbedding : SubcategoryWitness A C i → Embedding A C i
```

This is Lemma 3.1.5 in the book.

Proof idea:

- `SubcategoryWitness` gives a pullback criterion for every test category `X`.
- Use the criterion with a suitable test shape to identify objects and arrows of `A` over `C`.
- Combine with the arrow-map embedding part to show that the diagonal/self-pullback comparison
  `A → A ×_C A` is an equivalence.

This is likely the hardest theorem in the subcategory cluster.  It may require auxiliary lemmas
connecting:

- `mapCat terminalCat A` with `coreCat A` or objects of `A`;
- arrow embeddings with equality/equivalence of parallel objects in the self-pullback;
- Rezk-style object/arrow reconstruction.

Do not block the earlier phases on this theorem.  But closing it is high value because
`isoProjectionEmbedding` in `Chapter1/IsoRezk.lean` depends on it.

## Phase 6: identity and initial subcategories

Targets:

```lean
idSubcategoryWitness
initialSubcategoryWitness
```

### Identity functor

For `idFunctor C`, the arrow-action map is equivalent to the identity on `mapCat intervalCat C`, so
its embedding witness should be `identityEmbedding`.  The pullback criterion should reduce to the
identity pullback square for the square comparing `arrowActionMapFunctor` with itself.

Expected ingredients:

- unitors for composition with `idFunctor`;
- `identityEmbedding`;
- pullback uniqueness/equivalence packaging.

This is coherence-heavy but conceptually straightforward.

### Initial inclusion

For `initialElim C : initialCat → C`, use strict initiality and uniqueness out of `initialCat`.
The relevant mapping categories out of and into `initialCat` should be contractible/initial in the
right way.  This may need helper lemmas about functor categories with initial source and about
mapping anima of the initial category.

This target is lower priority than the full-subcategory and total-collection work.

## Phase 7: full-subcategory core comparison

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
2. Map `P` to `(fullSubcategory C P)^≃` using the full-subcategory lift for the composite
   `objectCollectionCat C P → coreCat C → C`.
3. Use full-subcategory lift β/uniqueness and the core universal property to build unit and counit.

Likely dependencies:

- `fullSubcategoryInclLands`;
- `fullSubcategoryLift`, `fullSubcategoryLiftBeta`, `fullSubcategoryLiftUniq`;
- `coreLift`/`coreLiftUniq`;
- `subcategoryWitnessEmbedding` or an equivalent full-subcategory embedding theorem.

### `fullSubcategoryAllObjectsEquiv`

If `P ≃ C^≃`, then the full subcategory on `P` should be equivalent to `C`.

Possible proof routes:

1. Use `fullSubcategoryCoreEquiv` plus the hypothesis `P ≃ C^≃` to show the inclusion is strongly
   surjective, then apply the Fundamental Theorem after it is proved.
2. Use full-subcategory universal property directly to construct inverse data, avoiding the full
   Chapter 6 theorem.

This should be later than `fullSubcategoryCoreEquiv`.  It is probably not a first-weekend target.

## Suggested workshop deliverables

### Minimum useful deliverable

- Decide and document definitions of `LandsInObjectCollection` and
  `PreservesMorphismCollection` that match the book's factorization statements.
- Move or add projection helpers so future proofs can use the factorization data.
- Keep model obligations at zero temporary admitted-definition fields.

### First proof-producing deliverable

- Extend `subcategoryPackage` so `subcategoryInclWitness` is a projection.
- Close `subcategoryInclWitness`.
- Adjust downstream projection paths for `subcategoryInclPreserves`, `subcategoryLift`, β, and
  uniqueness.

### Second proof-producing deliverable

- Close `all_morphisms_contains_identities` and `all_morphisms_closed`, assuming Phase 1 definitions.

### Third proof-producing deliverable

- Close `landsInObjectCollectionPreservesFull` and `fullSubcategoryInclLands`.

### Later deliverable

- Close `fullSubcategoryCoreEquiv`.
- Attempt `subcategoryWitnessEmbedding`.

## Dependency and priority table

| Declaration | Priority | Main blocker | Suggested action |
| --- | --- | --- | --- |
| `subcategoryInclWitness` | very high | not projected by `subcategoryPackage` | add `SubcategoryWitness` to Axiom H package |
| `all_morphisms_contains_identities` | high | admitted `containsIdentities` package | define identity-factorization structure |
| `all_morphisms_closed` | high | admitted `closedUnderComposition` package | define composite-factorization structure |
| `landsInObjectCollectionPreservesFull` | high | primitive landing/preservation structures | expose factorization data |
| `fullSubcategoryInclLands` | high | same, plus identity-arrow coherence | prove after landing/preservation refactor |
| `fullSubcategoryCoreEquiv` | medium/high | needs full-subcategory landing and core calculus | later theorem |
| `fullSubcategoryAllObjectsEquiv` | medium | likely needs Chapter 6 or direct inverse construction | later theorem |
| `subcategoryWitnessEmbedding` | high but hard | Lemma 3.1.5 proof infrastructure | separate theorem project |
| `idSubcategoryWitness` | medium | coherence | after witness helpers |
| `initialSubcategoryWitness` | lower | initial/functor-category lemmas | later |

## Anti-patterns

- Do not close side-structure goals with arbitrary primitive inhabitants.
- Do not turn every theorem in this cluster into a new `lf_opaque` field.  Add source axiom data only
  when it is genuinely part of Axiom H or the full-subcategory construction.
- Do not define full subcategories as strict equalities on objects.  The object collection is a
  subobject of the core, not a Lean predicate on raw terms.
- Do not use ordinary 1-categorical subcategory reasoning where the SCT statement is mapping-anima
  or core-based.
- Do not combine the representation refactor with large theorem proofs in one commit.

## Acceptance checks

For a representation refactor:

```bash
lake env lean InternalMath/SCT/Spec/Chapter3/Subcategories.lean
lake env lean InternalMath/SCT/Spec/Chapter3/FullSubcategoryLifts.lean
lake build InternalMath.SCT.Spec
lake build InternalMath.SCT.Model
```

For a proof-only change in a split module, check that module and the aggregate:

```bash
lake env lean InternalMath/SCT/Spec/Chapter3/FullSubcategoryLifts.lean
lake build InternalMath.SCT.Spec
```

After any completed tranche, run:

```lean
import InternalMath.SCT.Spec
#lint_type_theory_sorries SCT
#check_model_obligations SCT
```

Expected progress should be stated by naming which admitted declarations disappeared from the lint
output.  If model obligations change, explain which new field is book axiom data and which book
statement it represents.
