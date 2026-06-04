# SCT model formalization blueprints

Status: refreshed after the SCT IML reorganization and model-status audit, 2026-06-04.

Scope: these notes are for closing and organizing work around `InternalMath/SCT/Model.lean` and the
model workshop files under `InternalMath/SCT/IML/Model/`. They do not propose changes to
`InternalMath/SCT/Spec.lean`; internal-theory projects are tracked in
`Docs/SCT/IML/Internal/SCTInternalWorkshopBlueprints.md`.

The model file currently has the main carriers and a substantial first layer in place:

- `Anima` is `SSet.Kan`, the bundled full subcategory of Kan complexes in simplicial sets;
- `SCat` is `SSet.QCat`, the bundled full subcategory of quasicategories;
- functors are maps of simplicial sets between bundled quasicategories;
- natural transformations are 2-cells in mathlib's strict bicategory on `SSet.QCat`;
- natural isomorphisms are invertible bicategorical 2-cells;
- bicategorical adjunction data supplies the Chapter 5 adjunction type and unit/counit fields;
- the terminal anima, empty category, walking arrow, identities, composition, binary products,
  ordinary-category nerves, finite shapes, pullback/pushout indexing shapes, strict initiality, and
  several strict comparison fields are already supplied.

Since the previous refresh, the finite-shape package moved to `InternalMath/SCT/IML/Model/`,
`initialStrict` and `qcatCatEquivOfIso` are implemented, and the generated model's
`simplex2Face*` fields now refer to `SegalComposition.ModelBridge`. The remaining work there is the
actual bridge between `[2]` and `Fun([1],[1])`, not basic finite-shape bookkeeping.

`Model.lean` still contains a local section named `UpstreamFunctorQuasicategorySkeleton`. Its
remaining `sorry`s are upstream API assumptions, not local contributor proof obligations. They now
mainly represent the functor-quasicategory/internal-hom closure, curry/uncurry, and bridge APIs
being developed in `emilyriehl/infinity-cosmos` and mathlib PRs such as #35287. Local work should
either build on this adapter or replace it with upstream APIs when they land; contributors should
not spend workshop time trying to prove those local `sorry`s directly.

## Classification labels

Use these labels when selecting workshop projects.

- **Agent-friendly**: mostly packaging, endpoint bookkeeping, extensionality, or tedious Lean work;
  good for a coding assistant or a participant who wants implementation practice.
- **Mixed**: mathematically standard but with enough design/orientation choices that a human should
  supervise the API shape.
- **Human-interest**: requires real mathematical/API design, source-faithfulness decisions, or a
  nontrivial upstream theorem.
- **Upstream-wait**: should be replaced by mathlib/infinity-cosmos material rather than proved
  locally in this repository.
- **Completed/reuse**: already implemented locally; keep as background or use the helper in later
  projects.

## Workshop target matrix

| Project | Section | Classification | Suggested role |
| --- | --- | --- | --- |
| Replace remaining functor-quasicategory skeleton | 1.1 | Upstream-wait | maintainer/human |
| Wrap upstream functor-category closed structure | 1.2 | Agent-friendly after upstream | agent |
| Equality-to-`NatIso` comparison fields | 1.3 | Agent-friendly | agent |
| Strict isomorphism to `CatEquivData` bridge | 1.4 | Completed/reuse | reference |
| Bridge bicategory 2-cells to functor-quasicategory objects | 2.1 | Mixed | agent + review |
| Product natural-transformation calculus / `prodUniq` | 2.2 | Agent-friendly after 2.1 | agent |
| Finite-shape package and `[2] ≃ Fun([1],[1])` bridge | 2.3 | Mixed | paired work |
| Segal composition/unit/associativity | 2.4 | Mixed/Human-interest | human + agent |
| Invertible morphisms, `Iso(C)`, Rezk | 2.5 | Human-interest | human |
| Maximal Kan cores and mapping anima | 2.6 | Human-interest | human/upstream |
| Inverting functor categories and localization | 2.7 | Human-interest | human |
| Empty simplicial sets and `initialStrict` | 3.1 | Completed/reuse | reference |
| Coproduct closure and `coprodUniq` | 3.2 | Agent-friendly/Mixed | agent + review |
| Vertex-spanned full subcomplexes | 3.3 | Agent-friendly | agent |
| Kan-complex closure operations | 3.4 | Mixed | split agent/human |
| Fibration-stable pullbacks | 3.5 | Human-interest | human |
| Finite ordinary nerve wrappers and shape maps | 3.6 | Agent-friendly | agent |
| Context-layer semantics | 2.8 | Human-interest design | human |

## Current mathlib coverage notes

Already available in the current mathlib checkout:

- `CategoryTheory.nerve`, `CategoryTheory.nerveMap`;
- `CategoryTheory.Nerve.quasicategory`;
- `SSet.stdSimplex.isoNerve n`;
- `CategoryTheory.nerve.representableBy`;
- `CategoryTheory.nerve.homEquiv`, `CategoryTheory.nerve.edgeMk`,
  `CategoryTheory.nerve.homEquiv_comp`;
- `CategoryTheory.nerveFunctor.fullyfaithful`, `CategoryTheory.nerveAdjunction`;
- `CategoryTheory.hoFunctor.preservesFiniteProducts`;
- `SSet.prodStdSimplex.isoNerve`;
- `SSet.QCat.strictBicategory`, including hom-category 2-cells, whiskering, horizontal
  composition, and strict unit/associativity laws;
- `Bicategory.Adjunction` for bicategorical adjunction data.

Current gaps relevant to the model:

- cartesian closure of quasicategories under simplicial internal hom;
- a bridge between bicategory 2-cells and objects/edges of the functor quasicategory;
- a mature equivalence-edge/coherent-isomorphism API for interval-shaped morphisms and cores;
- maximal Kan cores and functoriality of cores;
- coproduct closure for quasicategories/Kan complexes as packaged theorems;
- homotopy/∞-categorical pullbacks of quasicategories;
- quasicategorical/Dwyer--Kan localization;
- context/fibration/universe semantics for the later chapters.

# Section 1: Direct functor-quasicategory skeleton projects

These projects are the straightforward work related to the local skeleton in `Model.lean`.
Some are not good local proof projects until upstream mathlib APIs land.

## 1.1 Replace remaining `UpstreamFunctorQuasicategorySkeleton` pieces by upstream APIs

### Classification

**Upstream-wait**, with a human maintainer reviewing the replacement.

### Current status

The QCat bicategory refactor closed the local natural-transformation composition, invertibility,
whiskering, horizontal-composition, and adjunction fields. Those are no longer upstream-wait local
`sorry`s.

### Model declarations

Remaining local skeleton declarations:

- `quasicategoryInternalHom`;
- `curryBeta`, `curryEta`, `curryNatIso`, `uncurryNatIso`;
- `curryUncurryForward`, `curryUncurryBackward`, `curryUncurryUnit`,
  `curryUncurryCounit`;
- the future bridge from bicategory 2-cells to the explicit `natTransObject`/functor-quasicategory
  package.

### Work plan

When mathlib/infinity-cosmos APIs land:

1. import the upstream modules;
2. replace local structures by aliases or thin wrappers;
3. preserve local helper names used by `sctModel` where practical;
4. delete local `sorry`s that become direct applications of upstream theorems;
5. keep a compatibility layer only for SCT-specific universe or field-order issues.

### Do not do

Do not try to prove the skeleton `sorry`s locally as workshop exercises. They are waiting for
upstream quasicategory/coherent-isomorphism infrastructure.

## 1.2 Functor quasicategory and closed-structure wrappers

### Classification

**Agent-friendly after upstream**. Currently mostly **Upstream-wait** because the key closure
theorem is missing locally.

### Model fields

- `funCat`;
- `precompFunctor`, `postcompFunctor`;
- `evalFunctor`;
- `curryFunctor`, `uncurryFunctor`;
- `curryBeta`, `curryEta`;
- `curryNatIso`, `uncurryNatIso`;
- `curryUncurryForward`, `curryUncurryBackward`, `curryUncurryUnit`,
  `curryUncurryCounit`.

### Mathematical statement

For quasicategories `C` and `D`, the simplicial internal hom `D^C` is a quasicategory. The
cartesian closed structure gives evaluation and currying:

```text
Hom(T × C, D) ≃ Hom(T, Fun(C,D)).
```

### Lean plan

Once upstream closure is available, define a bundled helper:

```lean
noncomputable def qcatFunctorCategory (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  ⟨(ihom C.obj).obj D.obj, inferInstance-or-upstream-theorem⟩
```

Then wrap closed-monoidal maps with `ObjectProperty.homMk`. This is largely bookkeeping.

### Acceptance checks

- The object of `funCat C D` should be the simplicial internal hom, not the Lean hom-set.
- The β/η comparison fields should be `NatIso` data, i.e. invertible bicategorical 2-cells, not
  strict equality unless the target field really asks for strict equality.

## 1.3 Equality-to-`NatIso` comparison fields

### Classification

**Agent-friendly**. Many instances are already done in `Model.lean` using `natIsoOfEq`.

### Model fields

Already filled or mostly filled:

- `terminalUnique`;
- `initialUnique`;
- `prodBeta1`, `prodBeta2`, `prodEta`;
- left/right unitors and associator for strict functor composition.

Remaining nearby field:

- `prodUniq`, which needs product calculus rather than plain equality.

### Mathematical statement

Whenever two strict simplicial maps are equal, the identity 2-cell in the QCat hom-category gives a
natural isomorphism between them. This is the right way to turn strict simplicial-set universal
properties into SCT comparison fields.

### Lean plan

Use a helper of the form:

```lean
SCTModelHelpers.natIsoOfEq : F = G → SCTModelHelpers.NatIso C D F G
```

Before invoking it, prove the equality of morphisms in `SSet.QCat` by reducing to `.hom` and using
simplicial-set extensionality.

### Pitfalls

- Do not use this for fields where the input data only gives natural isomorphisms of projections,
  such as `prodUniq`. That needs Section 2.2.

## 1.4 Strict isomorphism to `CatEquivData` bridge

### Classification

**Completed/reuse**.

### Current status

`InternalMath/SCT/Model.lean` already provides:

```lean
SCTModelHelpers.qcatCatEquivOfIso
```

It packages a strict isomorphism of bundled quasicategories as equivalence data, using the
isomorphism and its inverse as forward/backward functors and equality-to-`NatIso` for the two
composites.

### Remaining use

Keep this helper as a one-way bridge for strict comparison isomorphisms, finite-shape transports,
and future strict curry/uncurry equivalences. Do not redefine `CatEquiv` as strict isomorphism.

# Section 2: Projects that build on the functor-quasicategory skeleton

These projects use the functor-category/NatIso interpretation but require additional construction
or design beyond replacing the skeleton.

## 2.1 Bridge bicategory 2-cells to functor-quasicategory objects

### Classification

**Mixed**. This is now the central bridge project for natural transformations: the mathematics is
standard, but the generated model expression is long and the API should match incoming
functor-quasicategory work.

### Model fields

- `natTransObject`;
- `functorObjectSourceCompat`;
- `functorObjectTargetCompat`;
- `objectwiseNatIsoComponent`.

### Mathematical statement

In the current model, a natural transformation `α : F ⟶ G` is a morphism in the hom-category
`Ho(Fun(A,C))`. The functor-quasicategory API should connect such a 2-cell with an object of the
explicit natural-transformation category used by SCT, i.e. with the corresponding edge or homotopy
class of edges in `Fun(A,C)`. Evaluation at an object `x : terminalCat → A` should then produce an
interval-shaped morphism in `C`.

For a natural isomorphism, `α` is invertible in `Ho(Fun(A,C))`. Under evaluation at `x`, it should
become an invertible interval-shaped morphism in `C`. This is the semantic content of
`objectwiseNatIsoComponent`.

### Lean plan

1. Use the incoming functor-quasicategory API to define or choose the object classified by a
   bicategory 2-cell `α : F ⟶ G`.
2. Show this object is the generated `natTransObject` expression and has the expected source and
   target compatibilities.
3. Define evaluation at an object from `evalFunctor A C` and the product pairing with `x`.
4. Prove that evaluation sends invertible 2-cells to invertible interval-shaped morphisms, using the
   equivalence between isomorphisms in the hom-category and equivalence edges in the internal hom.

### Acceptance checks

- Objectwise invertibility should be derived, not stored as extra independent data.
- Do not replace the bridge by a strict equality or arbitrary representative choice without the
  homotopy-class compatibility proof.
- Endpoint orientation should be tested separately before closing the model field.

## 2.2 Product natural-transformation calculus and `prodUniq`

### Classification

**Agent-friendly after 2.1**, with a small amount of API design.

### Model field

- `prodUniq`.

### Mathematical statement

The functor category into a product should be equivalent to the product of functor categories:

```text
Fun(Γ, C × D) ≃ Fun(Γ,C) × Fun(Γ,D).
```

A natural isomorphism `H ≅ K` into `C × D` is determined by natural isomorphisms of its two
projections.

### Lean plan

Prove or import a comparison:

```lean
-- schematic only
def funCatProductComparison (Γ C D : SSet.QCat.{u}) :
    funCat Γ (qcatProduct C D) ≅ qcatProduct (funCat Γ C) (funCat Γ D)
```

Then build the product natural isomorphism by pairing the two input invertible 2-cells and
transporting across this comparison.

### Pitfalls

Do not prove `prodUniq` by strict equality of `H` and `K`; its hypotheses are natural isomorphisms
of projections, not equalities.

## 2.3 Finite shapes and the `[2] ≃ Fun([1],[1])` bridge

Status: finite-shape package implemented in `InternalMath/SCT/IML/Model/FiniteShapes.lean`; the
model-facing `[2]`/`Fun([1],[1])` gap is now isolated in `SegalComposition.ModelBridge`.

### Classification

**Mixed**. The finite-shape bookkeeping is checked; the remaining bridge is a small but real
mathematical identification.

### Model fields

Already connected to checked or project-file declarations:

- `simplex2Id0`, `simplex2Can`, `simplex2Id1`;
- `simplex2Face01`, `simplex2Face12`, `simplex2Face02`;
- `simplex2Deg0`, `simplex2Deg1`;
- endpoint beta fields for faces and degeneracies.

Still dependent on later bridge work:

- `natTransObject`;
- square lower/upper triangle, restriction, and extension fields;
- Segal restriction/extension fields after the horn-map package.

### Mathematical statement

Finite indexing shapes such as `[0]`, `[1]`, `[2]`, and `[1] × [1]` are nerves of finite ordinary
categories. Their maps are induced by monotone maps of finite ordinals. These wrappers provide the
coordinate system for natural transformations, squares, and Segal restrictions.

The generated SCT model presents `simplex2Cat` as `Fun([1],[1])`, not as the standalone standard
simplex `[2]`. The remaining bridge identifies the three relevant edges of `Fun([1],[1])` with the
curried monotone maps:

```text
min        : [1] × [1] -> [1]
max        : [1] × [1] -> [1]
projection : [1] × [1] -> [1]
```

### Lean status and plan

Implemented:

1. bundled `[0]`, `[1]`, and `[2]` quasicategories using standard simplices, with nerve
   identifications for finite ordinals;
2. simplex maps, cofaces, codegeneracies, and oriented `[2]` face maps;
3. endpoint beta lemmas for `[2]` faces and the interval degeneracy `[1] -> [0]`;
4. `[1] × [1]` as a product quasicategory, with projections, vertices, horizontal/vertical edges,
   and a nerve identification with the product poset;
5. span and cospan shapes as nerves of mathlib walking span/cospan categories;
6. project-file declarations for the generated model's three `simplex2Face*` maps and endpoint
   comparisons, in `SCTSegalCompositionSkeleton.ModelBridge`.

Still to do:

1. replace the `ModelBridge` declarations by actual curried `min`, `max`, and projection maps;
2. add any extra square lower/upper-triangle inclusions required by the Segal/square calculus;
3. connect interval-shaped functors with bicategory natural-transformation 2-cells through the
   `natTransObject` bridge.

### Pitfalls

- Do not use ordinary-category composition to model composition in an arbitrary target
  quasicategory. Ordinary nerves are only indexing shapes here.
- Face orientation should be checked in small probes before filling fields.

## 2.4 Segal composition, unit, and associativity package

Detailed workshop blueprint: `Docs/SCT/IML/Model/SegalCompositionBlueprint.md`.
Companion Lean scaffold: `InternalMath/SCT/IML/Model/SegalComposition.lean`.

### Classification

**Mixed/Human-interest**. The proofs are standard but involve choices of fillers and coherence
orientation.

### Model fields

- `segalRestriction`, `segalExtension`, `segalUnit`, `segalCounit`;
- `compositeSourceCompat`, `compositeTargetCompat`;
- `composeLeftUnit`, `composeRightUnit`, `composeAssoc`;
- `horizCompIdId`, `horizCompCompComp`, `horizCompLeftId`, `horizCompRightId`;
- `assocFunctorNaturality`.

### Mathematical statement

Composition in a quasicategory is encoded by filling inner horns `Λ[2,1] → C`. The SCT model
fields package restriction to composable pairs, a chosen extension/filler, and the usual unit and
associativity comparisons as natural isomorphism data.

### Lean plan

Use the finite-shape package from 2.3, then define noncomputable fillers from
`SSet.Quasicategory.hornFilling`. Package comparisons through `NatIso`/bicategory 2-cell data
rather than asserting uniqueness on the nose.

### Pitfalls

- Filler choices are not unique strictly. Comparisons should live in `NatIso` data.
- This is too large for a first workshop exercise unless split into restriction/extension only.

## 2.5 Invertible morphisms, `Iso(C)`, and Rezk equivalence

Detailed workshop blueprint: `Docs/SCT/IML/Model/IsoRezkModelBlueprint.md`.
Companion Lean scaffold: `InternalMath/SCT/IML/Model/IsoRezkModel.lean`.

### Classification

**Human-interest**.

### Model fields

- `invertibleMorphismInverse`;
- `invertibleMorphismInverseSource`, `invertibleMorphismInverseTarget`;
- `invertibleMorphismLeftUnit`, `invertibleMorphismRightUnit`;
- `invertibleMorphismObjectPackage`;
- `rezkEquiv`.

### Mathematical statement

An interval-shaped morphism is invertible when its underlying edge is an equivalence edge in `C`.
The inverse arrow comes from the inverse edge. `Iso(C)` should be the full subcategory of
`Fun([1],C)` spanned by invertible arrows, and the Rezk equivalence should compare objects with
isomorphisms as in the book.

### Dependencies

- objectwise evaluation from 2.1;
- finite/Segal package from 2.3 and 2.4;
- full-on-vertices subcategories from 3.3;
- maximal-core/equivalence-edge API from 2.6 or upstream.

### Pitfalls

Do not define `Iso(C)` using `rezkEquiv`; that is circular.

## 2.6 Maximal Kan cores and mapping anima

Detailed workshop blueprint: `Docs/SCT/IML/Model/MaximalKanCoreMappingAnimaBlueprint.md`.
Companion Lean scaffold: `InternalMath/SCT/IML/Model/MappingAnima.lean`.

### Classification

**Human-interest**, likely upstream-facing.

### Model fields

- `mapAnima`;
- `coreIncl`;
- `coreUniversalPackage`;
- `groupoidConstArrowFunctor`;
- `groupoidIntervalEquiv`;
- `animaOfGroupoidEquiv`.

### Mathematical statement

Every quasicategory `C` has a maximal Kan subcomplex `C^≃` containing all vertices and exactly the
equivalence edges. The mapping anima should be:

```text
Map(C,D) := Fun(C,D)^≃.
```

### Required API

- equivalence-edge predicate and closure operations;
- maximal core subcomplex;
- proof the core is Kan;
- functoriality of the core;
- universal property for maps from Kan complexes/groupoids.

### Pitfalls

Do not use `SSet.KanComplex C.obj` as a fake groupoid witness for arbitrary quasicategories. That
is only valid when the object is already Kan.

## 2.7 Inverting functor categories and localization

### Classification

**Human-interest**, after several smaller pieces exist.

Detailed workshop blueprint: `Docs/SCT/IML/Model/LocalizationBlueprint.md`.
Companion Lean scaffold: `InternalMath/SCT/IML/Model/Localization.lean`.

### Model fields

- `invertingFunctorObjectPackage`;
- `localizationCat`;
- `localizationFunctor`;
- `localizationUniversalPackage`.

### Mathematical statement

A functor inverts a morphism collection when the induced map on arrow objects lands in the
invertible-arrow subcategory of the target. Localization is the quasicategorical universal category
receiving such a functor.

### Recommended split

1. Build full subcategories first (3.3).
2. Build invertible-arrow objects (2.5).
3. Define inverting-functor subcategories using the functor-category skeleton.
4. Wait for or assume a real quasicategorical localization construction.

### Pitfalls

Do not use ordinary localization of the homotopy category as the SCT localization.

## 2.8 Context-layer semantic design checkpoint

### Classification

**Human-interest design project**.

### Model fields

- `ContextCat`, `ContextFunctor`, `ContextNatIso`, `ContextCatEquiv`;
- weakening and reindexing fields;
- context terminal/initial/product/coproduct/pullback/functor-category fields;
- `sigmaCat`, `sigmaProjection`, `sigmaLift`, and comparison fields;
- context fibration and cocartesian/cartesian witness fields.

### Design questions

- Are contexts all quasicategorical fibrations over a base, or a chosen split class?
- Which fields require strict split pullback data rather than equivalence over the base?
- How do context natural isomorphisms relate to equivalence edges over a base?
- Which context fields are transports of non-context fields, and which need separate fibration
  theorems?

### Recommended workshop output

A short design note is a better output than code. If code is attempted, implement only a tiny
vertical slice after the design is agreed.

# Section 3: Projects independent of the functor-quasicategory skeleton

These projects do not depend essentially on the functor-quasicategory skeleton. Some final model
fields may use `NatIso` or `CatEquivData` for packaging, but the main mathematical work is separate.

## 3.1 Empty simplicial sets and `initialStrict`

### Classification

**Completed/reuse**.

### Current status

`initialStrict` is implemented in `InternalMath/SCT/Model.lean`. The proof uses reusable local
helpers showing that a map to the empty-nerve quasicategory forces the source to have no vertices,
and that maps out of a quasicategory with no vertices are unique. It then packages the two strict
composite equalities with `natIsoOfEq`.

### Remaining use

Keep these helpers available for later empty-shape or initiality arguments. This is no longer a
workshop target unless someone wants to polish or upstream the underlying simplicial-set lemmas.

### Pitfall

Do not eliminate a higher simplex directly. First extract a vertex from it.

## 3.2 Coproduct closure and coproduct natural-isomorphism calculus

### Classification

**Agent-friendly/Mixed**. Good workshop target with review.

### Model fields

Implemented modulo the local coproduct-closure assumption:

- `coprodCat`, `coprodIn1`, `coprodIn2`, `coprodCase`;
- `coprodBeta1`, `coprodBeta2`, `coprodEta`.

Still open:

- proof of `quasicategoryCoprod`, currently a local helper `sorry`;
- `coprodUniq`;
- base-change and disjointness equivalences.

### Mathematical statement

Coproducts of quasicategories are simplicial-set coproducts. An inner horn is connected, so a map
from an inner horn into a binary coproduct lands in one summand. Fill there and include the filler
back into the coproduct.

### Lean plan

1. Prove or import a reusable closure lemma for quasicategory coproducts.
2. Keep the existing wrappers for injections, case maps, and β/η comparisons.
3. Use Section 2.2-style natural-transformation calculus for `coprodUniq`.
4. Treat base-change and disjointness as later equivalence-data projects, not as strict equalities.

### Pitfalls

The connectedness argument should be stated cleanly. Avoid pointwise hacks that lose naturality.

## 3.3 Vertex-spanned full subcomplexes and full subcategories

### Classification

**Agent-friendly** for the subcomplex/quasicategory-closure theorem. Later semantic packages are
**Mixed**.

### Model fields

- `subcategoryPackage`, for the full-subcategory special case;
- `fullSubcategoryMorphismComprehensionPackage`;
- support for `invertibleMorphismObjectPackage` and `invertingFunctorObjectPackage` later.

### Mathematical statement

Given a quasicategory `C` and a predicate on vertices, the full simplicial subset spanned by those
vertices is again a quasicategory. An `n`-simplex belongs exactly when all of its vertices satisfy
the predicate.

### Lean plan

Define:

```lean
-- schematic only
def SSet.Subcomplex.fullOnVertices (C : SSet.{u}) (P : C _⦋0⦌ → Prop) : C.Subcomplex
lemma quasicategory_fullOnVertices (C : SSet.{u}) [SSet.Quasicategory C] ... :
    SSet.Quasicategory (fullOnVertices C P).toSSet
```

The horn filler in `C` has the same vertices as the horn, so it lies in the full subcomplex.

### Pitfalls

This only handles full subcategories. Non-full subcategories selected by morphism collections need
more structure.

## 3.4 Kan-complex closure operations for anima

### Classification

**Mixed**.

### Model fields and helpers

- better product/coproduct helpers for `GroupoidWitness`;
- `equiv_to_anima_is_anima`, once equivalence has a real meaning;
- `sigma_anima_indexed_is_anima`, after anima-indexed families are interpreted.

### Split by difficulty

Agent-friendly pieces:

- terminal Kan complex helper, already present;
- products of Kan complexes;
- coproducts of Kan complexes, if coproduct closure is developed for simplicial sets.

Human-interest pieces:

- if a quasicategory is equivalent to a Kan complex, then it is a Kan complex;
- dependent sums of anima-indexed families.

### Pitfalls

Do not use equivalence-to-anima closure until `CatEquiv` has the intended semantics.

## 3.5 Fibration-stable pullbacks and homotopy pullbacks

Detailed workshop blueprint: `Docs/SCT/IML/Model/FibrationStablePullbacksBlueprint.md`.
Companion Lean scaffold: `InternalMath/SCT/IML/Model/FibrationPullbacks.lean`.

### Classification

**Human-interest** for the general SCT fields; **Mixed** for narrowly hypothesized strict pullback
lemmas.

### Model fields

- `pullbackCat`, `pullbackPr1`, `pullbackPr2`, `pullbackComm`, `pullbackLift`;
- `pullbackBeta1`, `pullbackBeta2`, `pullbackUniq`, `pullbackEta`;
- directed pullback and fibration-stability fields later.

### Mathematical statement

The SCT pullback should be an ∞-categorical/homotopy pullback in `Cat_∞`. A strict simplicial
pullback is valid only under suitable fibration hypotheses or as a model for a homotopy pullback
with extra structure.

### Recommendation

Do not try to close the general `pullbackCat` block as a local workshop project. A narrower useful
project is to prove pullback stability for quasicategories under an explicit inner-fibration or
isofibration hypothesis, then document exactly which SCT fields it does and does not close.

## 3.6 Ordinary-category nerve wrappers and finite shapes

### Classification

**Agent-friendly**, mostly already done.

### Model fields and helpers

- `initialCat`, `intervalCat`;
- `pullbackShapeCat`, `pushoutShapeCat`;
- finite shapes used by simplex, square, and Segal packages.

### Mathematical statement

Mathlib already proves that ordinary-category nerves are quasicategories and provides maps induced
by functors. The local work is naming wrappers and avoiding universe friction.

### Lean plan

Continue using:

```lean
SCTModelHelpers.qcatNerve
SCTModelHelpers.qcatNerveMap
```

Add named finite-shape wrappers only when a later field needs them.

## 3.7 Standard simplices, finite-nerve edge calculus, and square shapes

### Classification

**Agent-friendly/Mixed**.

### Uses

- finite shape sanity checks;
- endpoint orientation for Section 2.3;
- square restriction/extension fields;
- comparison between `Δ[n]` and finite ordinal nerves.

### Mathematical statement

`SSet.stdSimplex.isoNerve n` and `SSet.prodStdSimplex.isoNerve p q` identify standard simplices
and products of standard simplices with finite ordinary nerves. These are ideal for shape-level
bookkeeping.

### Lean plan

Package reusable lemmas for:

- standard simplex quasicategory instances;
- edges in nerves of finite preorders;
- the two paths through `[1] × [1]`;
- face and degeneracy orientation tests.

### Pitfalls

These lemmas should support shape bookkeeping. They should not replace quasicategory composition
in arbitrary targets.

## 3.8 `hoFunctor` and strict-bicategory sanity checks

### Classification

**Mostly completed for `NatIso`; still useful for probes.**

### Purpose

Mathlib's strict bicategory of quasicategories now supplies the model semantics for `NatTrans`,
`NatIso`, whiskering, horizontal composition, and bicategorical adjunctions. `hoFunctor` product
preservation and strict-bicategory probes are still useful for orientation and product behavior, but
they do not by themselves construct mapping anima or the `natTransObject` bridge.

# Postponed or non-workshop targets

Postpone these unless a participant specifically wants a research/design project:

- general homotopy pullbacks in `Cat_∞`;
- full directed-univalence and universe fields;
- straightening/unstraightening and universal cocartesian fibration fields;
- context semantics without a prior design note;
- local proof of the upstream functor-quasicategory skeleton `sorry`s.

# Recommended workshop project menu

Good agent-heavy projects:

1. Vertex-spanned full subcomplexes and quasicategory closure (3.3).
2. Coproduct closure and `coprodUniq`, with review of the connectedness argument (3.2).
3. Square/Segal finite-shape orientation tests beyond the already checked base package (2.3, 3.7).
4. Equality-to-`NatIso` cleanup around remaining strict comparison fields (1.3).
5. Reuse of `initialStrict` and `qcatCatEquivOfIso` in later fields, rather than new work on them.

Good human-led projects:

1. Maximal Kan core API and mapping anima (2.6).
2. `Iso(C)` and Rezk equivalence without circularity (2.5).
3. Context-layer semantic design (2.8).
4. Fibration-stable or homotopy pullback semantics (3.5).
5. Quasicategorical localization (2.7).

Good paired projects:

1. Bridge bicategory 2-cells to functor-quasicategory objects (2.1).
2. Product natural-transformation calculus and `prodUniq` (2.2).
3. `[2] ≃ Fun([1],[1])` bridge plus Segal-composition package (2.3, 2.4).
4. Coproduct closure plus universal-property fields (3.2).
