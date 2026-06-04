# Maximal Kan cores and mapping anima blueprint

Status: synced with QCat bicategory two-cell model decision, 2026-06-03.

Scope: this note expands the project around `mapAnima`, groupoid cores, and maximal Kan cores in
`InternalMath/SCT/Model.lean`.  It is written for human workshop participants.  The companion Lean
scaffold is `InternalMath/SCT/IML/Model/MappingAnima.lean`.

## Short version

The intended model interpretation is:

```text
core(C)      := C^≃
Map(C,D)    := Fun(C,D)^≃
Map_C(x,y)  := fiber of Map([1],C) → Map(*,C) × Map(*,C) at (x,y)
```

Here `(-)^≃` denotes the maximal Kan subcomplex: it contains all vertices and precisely the
equivalence edges.  This project should provide a real maximal-core API and then use it to interpret
the SCT mapping-anima and core fields.

Current model note: `InternalMath.SCT.Model` interprets `NatTrans` as 2-cells in mathlib's strict
bicategory of quasicategories, and `NatIso` as invertible 2-cells.  This blueprint and the scaffold
still concern raw equivalence edges inside quasicategories and maximal cores.  The bridge from
bicategory 2-cells to objects or edges of `Fun(C,D)` belongs to the future `natTransObject` API.

## Why this is a human workshop project

This is mathematically standard, but the useful Lean API depends on design choices:

- which upstream equivalence-edge notion to expose;
- whether the maximal core is stored as a subcomplex or as a bundled Kan complex with inclusion;
- how to phrase the universal property so it matches SCT Axiom G;
- how much to prove locally before replacing the scaffold with mathlib/infinity-cosmos APIs.

Agents can help with endpoint bookkeeping and subcomplex boilerplate after the design is fixed.
The first pass should be human-led.

## Existing SCT declarations involved

Primitive or model fields:

- `mapAnima : SCat → SCat → Anima`;
- `coreIncl`;
- `coreUniversalPackage`;
- `groupoidConstArrowFunctor`;
- `groupoidIntervalEquiv`;
- `animaOfGroupoidEquiv`.

Important derived declarations already in `Spec.lean`:

- `coreAnima C := mapAnima terminalCat C`;
- `coreCat C := animaCat (coreAnima C)`;
- `coreGroupoid`;
- `coreLift`, `coreLiftBeta`, `coreLiftUniq`;
- `coreFunctor`;
- `mapAnimaCoreEquiv : animaCat (mapAnima C D) ≃ coreCat (funCat C D)`;
- `morphismAnima C := coreAnima (funCat intervalCat C)`;
- `objectHomCat C x y`, the category-level fixed-endpoint arrow object.

The model should make these agree with the quasicategorical semantics instead of adding new
primitive data.

## Mathematical targets

### Target A: equivalence edges

Choose or wrap an upstream notion of equivalence edge in a quasicategory.

Expected API shape:

```lean
EquivalenceEdge {X : SSet} [SSet.Quasicategory X] {x y : X _⦋0⦌}
  (e : SSet.Edge x y) : Prop
```

Needed operations:

1. identity edges are equivalences;
2. equivalences are closed under inverse and composition;
3. simplicial maps preserve equivalence edges;
4. equivalent definitions, such as inverse-edge data with two triangle fillers, are connected;
5. compatibility with the functor-quasicategory bridge from equivalence edges to invertible
   bicategory 2-cells.

Design question: should the SCT adapter use a proposition, data, or both?  The maximal-core
subcomplex wants a proposition.  Invertible interval-shaped morphism packages often want data, while
`NatIso` is now an invertible 2-cell in the QCat bicategory.  One reasonable split is a Prop-valued
membership predicate plus a separate structure providing chosen inverse data when needed.

### Target B: maximal core subcomplex

For a quasicategory `C`, define a subcomplex `C^≃ ⊆ C`.

Expected API shape:

```lean
maximalCoreSubcomplex (C : SSet.QCat) : C.obj.Subcomplex
```

Properties:

1. every vertex of `C` lies in `C^≃`;
2. a 1-simplex lies in `C^≃` iff it is an equivalence edge;
3. higher simplices are included exactly when all edges are equivalences, or by an equivalent
   source-faithful characterization;
4. the inclusion is a monomorphism/subcomplex inclusion.

Human choice: decide whether higher-simplex membership should be defined by all edges, all spine
edges, or pulled from an upstream maximal-core construction.  The all-edges definition is easy to
state and often convenient for subcomplex closure; the upstream API may choose another defeq shape.

### Target C: the maximal core is Kan

Prove:

```lean
SSet.KanComplex (maximalCoreSubcomplex C : SSet)
```

This is the main mathematical proof.  It should probably not be invented ad hoc in `Model.lean`.
Possible routes:

1. use a mathlib/infinity-cosmos theorem directly;
2. port the standard proof that the largest Kan subcomplex of a quasicategory is Kan;
3. define the core via an upstream construction already known to be Kan.

Acceptance criterion: the result should not assume `SSet.KanComplex C.obj` for an arbitrary
quasicategory.  That would make every quasicategory a groupoid and is semantically wrong.

### Target D: universal property for maps from anima/Kan complexes

A map from a Kan complex into a quasicategory sends every edge to an equivalence edge, hence factors
through the maximal core.

Expected API shape:

```lean
liftFromKan (A : SSet) [SSet.KanComplex A] (C : SSet.QCat) (F : A ⟶ C.obj) :
  A ⟶ (maximalCore C).obj

liftFromKan_fac : liftFromKan A C F ≫ coreIncl C = F
liftFromKan_uniq : L ≫ coreIncl C = F → L = liftFromKan A C F
```

This strict simplicial-set factorization is the model-side source for SCT's `coreUniversalPackage`.
The SCT package itself asks for functors, natural isomorphisms, and uniqueness in the synthetic
language, so there will be an adapter layer from strict subcomplex factorization to the generated
model fields.

### Target E: functoriality of the core

For a functor of quasicategories `F : C ⟶ D`, define:

```text
F^≃ : C^≃ ⟶ D^≃
```

using preservation of equivalence edges by simplicial maps.

This supports:

- `coreFunctor` in the internal theory;
- postcomposition on mapping anima;
- functoriality of object/morphism collections.

### Target F: mapping anima

Once `Fun(C,D)` is available as a quasicategory, define:

```text
Map(C,D) := Fun(C,D)^≃.
```

For the current model, this probably means:

1. use the functor-quasicategory skeleton or its upstream replacement to get `funCat C D`;
2. apply the maximal-core construction;
3. bundle the result as `SSet.Kan`/`Anima`;
4. define the comparison with `coreCat (funCat C D)` by construction, not by an arbitrary
   equivalence.

This is the interpretation of the primitive `mapAnima` model field.

### Target G: fixed-endpoint hom anima

The fixed-endpoint hom anima should be derived internally.  The clean SCT-side definition is:

```text
Map_C(x,y) := Map(*, objectHomCat C x y)
```

where `objectHomCat C x y` is already defined as the category of arrows from `x` to `y` using
endpoint fibers.  Equivalently, prove that this agrees with the homotopy fiber of

```text
Map([1], C) → Map(*, C) × Map(*, C)
```

at `(x,y)`.

This target should be a later theorem/API layer, not an extra primitive in the model.

## Suggested workshop split

### Project 1: upstream/API audit

Goal: identify the best existing equivalence-edge and maximal-core APIs.

Deliverables:

- a short note listing candidate mathlib/infinity-cosmos declarations;
- a decision on Prop-valued vs data-valued local wrappers;
- a replacement plan for the placeholders in `InternalMath/SCT/IML/Model/MappingAnima.lean`.

Good for: human maintainer plus one agent session for search/probes.

### Project 2: maximal-core subcomplex definition

Goal: define or wrap `maximalCoreSubcomplex`.

Deliverables:

- contains-all-vertices lemma;
- edge membership iff equivalence-edge lemma;
- subcomplex closure proof if the definition is local.

Good for: human-led paired implementation.

### Project 3: Kan proof for the core

Goal: prove or import that the maximal core is Kan.

Deliverables:

- `SSet.KanComplex (C^≃)`;
- a bundled `SSet.QCat`/Kan object helper;
- comments documenting the theorem source.

Good for: human-interest mathlib/infinity-cosmos work.

### Project 4: maps from Kan complexes factor through the core

Goal: build the universal property needed by Axiom G.

Deliverables:

- `liftFromKan`;
- factorization and uniqueness lemmas;
- adapter notes for `coreUniversalPackage`.

Good for: mixed human/agent work after Projects 2--3.

### Project 5: map anima adapter

Goal: replace the `mapAnima` and `coreIncl` model fields by maximal-core constructions.

Deliverables:

- `Map(C,D) = Fun(C,D)^≃` helper;
- `core(C) = Map(*,C)` helper;
- model-field candidates for `mapAnima`, `coreIncl`, and the core package.

Good for: agent-friendly after the previous projects and the functor-quasicategory skeleton land.

### Project 6: fixed-endpoint hom anima API

Goal: package `Map_C(x,y)` as a derived SCT construction.

Deliverables:

- internal definition, probably named `objectHomAnima` or similar;
- equivalence with the endpoint fiber of `Map([1],C)`;
- compatibility with existing `objectHomCat` contractibility fields.

Good for: human + agent after mapping anima and pullback/fiber APIs are stable.

## Lean scaffold

The file `InternalMath/SCT/IML/Model/MappingAnima.lean` currently contains these placeholders:

```lean
SCTMappingAnimaSkeleton.MaximalKanCore.EquivalenceEdge
SCTMappingAnimaSkeleton.MaximalKanCore.subcomplex
SCTMappingAnimaSkeleton.MaximalKanCore.mem_subcomplex_zero
SCTMappingAnimaSkeleton.MaximalKanCore.edge_mem_subcomplex_iff
SCTMappingAnimaSkeleton.MaximalKanCore.kanComplex
SCTMappingAnimaSkeleton.MaximalKanCore.qcat
SCTMappingAnimaSkeleton.MaximalKanCore.incl
SCTMappingAnimaSkeleton.MaximalKanCore.liftFromKan
SCTMappingAnimaSkeleton.MaximalKanCore.liftFromKan_fac
SCTMappingAnimaSkeleton.MaximalKanCore.liftFromKan_uniq
SCTMappingAnimaSkeleton.MappingAnima.obj
SCTMappingAnimaSkeleton.MappingAnima.kanComplex
SCTMappingAnimaSkeleton.MappingAnima.incl
```

The scaffold deliberately stops before filling `sctModel` fields.  It gives names and types for the
main mathematical seams while leaving the core proof and API choices for workshop participants.

## Informal proof or construction for each current Lean `sorry`

This section tracks every `sorry` currently present in `InternalMath/SCT/IML/Model/MappingAnima.lean`.
If the Lean scaffold changes, update this list in the same commit.

### `MaximalKanCore.EquivalenceEdge`

This is a definition rather than a theorem.  Define `EquivalenceEdge e` to mean that `e` is an
equivalence edge of a quasicategory.  A concrete local definition can use inverse-edge data: there
exists an edge `e⁻¹ : y ⟶ x` together with two 2-simplices witnessing `e ≫ e⁻¹` as the degenerate
identity at `x` and `e⁻¹ ≫ e` as the degenerate identity at `y`.  If mathlib/infinity-cosmos
provides a preferred predicate, make this an alias or theorem-equivalent wrapper around that
predicate.  The proof obligation is the choice of this definition and the equivalence with the
upstream API.

### `MaximalKanCore.subcomplex`

Define the core subcomplex by the rule: an `m`-simplex `σ : Δ[m] ⟶ C` lies in `C^≃` iff every edge
of `σ` is an equivalence edge of `C`.  Equivalently, quantify over every monotone map
`[1] → [m]` and require the restricted 1-simplex to be an equivalence edge.  To prove this is a
subcomplex, take a simplex whose edges are equivalences and precompose it with a simplex-operator
`[k] → [m]`.  Every edge of the resulting `k`-simplex is the restriction of an edge of the original
simplex, possibly degenerate.  Restrictions of equivalence edges are equivalences, and degenerate
identity edges are equivalences.  Hence the edge condition is stable under all face and degeneracy
maps.

### `MaximalKanCore.mem_subcomplex_zero`

A vertex `x : C₀` determines a 0-simplex.  The only edges of a 0-simplex, after restriction along
`[1] → [0]`, are degenerate identity edges at `x`.  Identity edges are equivalence edges, so the
0-simplex satisfies the defining edge condition for the core subcomplex.

### `MaximalKanCore.edge_mem_subcomplex_iff`

For a 1-simplex `e : x ⟶ y`, the edge restrictions of the corresponding simplex of `Δ[1]` are
`e` itself and the degenerate identities at the endpoints.  If the simplex lies in the core, then in
particular the nondegenerate edge `e` is an equivalence edge.  Conversely, if `e` is an equivalence
edge, then all edge restrictions of the 1-simplex are equivalence edges: `e` by assumption and the
endpoint degeneracies by identity-edge invertibility.  Thus membership in the core is equivalent to
`EquivalenceEdge e`.

### `MaximalKanCore.kanComplex`

Use the standard theorem that the maximal subcomplex of a quasicategory spanned by all vertices and
equivalence edges is a Kan complex.  The proof is by horn filling.  Given a horn in `C^≃`, view it
as a horn in `C`.  For inner horns, fill it using the quasicategory horn-filling property of `C`.
All edges of the resulting simplex are already edges of the horn, so they are equivalence edges and
the filler lands back in `C^≃`.  For outer horns, use the fact that the relevant boundary edge in
the core is an equivalence: choose inverse-edge/triangle data and convert the outer lifting problem
into inner horn lifting problems in `C`.  The resulting filler has all edges equivalent by closure
of equivalence edges under inverse and composition.  This gives fillers for all horns, so `C^≃` is
Kan.
A formal implementation should either import this theorem from upstream or formalize this standard
Joyal proof once the equivalence-edge calculus is available.

### `MaximalKanCore.liftFromKan`

Let `A` be a Kan complex and `F : A ⟶ C`.  Define the underlying map to the core by the same
simplicial map `F`, and prove its image lands in the subcomplex.  For any simplex of `A`, every edge
of its image in `C` is the image under `F` of an edge of `A`.  In a Kan complex every edge is an
equivalence: fill the two outer 2-horns to obtain inverse and unit-triangle data.  Simplicial maps
preserve equivalence edges.  Therefore every edge of every image simplex is an equivalence in `C`,
so `F` factors through `C^≃`.

### `MaximalKanCore.liftFromKan_fac`

The lift in the previous item is defined by giving the same levelwise function as `F`, with an
extra proof that each image simplex lies in the core subcomplex.  Composing with the subcomplex
inclusion forgets this proof.  Therefore the composite is definitionally, or by simplicial-map
extensionality, equal to the original map `F`.

### `MaximalKanCore.liftFromKan_uniq`

Suppose `L : A ⟶ C^≃` also composes with the core inclusion to `F`.  The inclusion of a subcomplex
is levelwise injective, and the equality `L ≫ incl = F` identifies the underlying simplex of `L a`
with the underlying simplex of the constructed lift at every simplex `a`.  By subtype/extensionality
for maps into a subcomplex, `L` equals the constructed lift.  Equivalently, use that the subcomplex
inclusion is a monomorphism and both maps have the same composite with it.

## Anti-patterns

Do not use any of these as shortcuts:

- `SSet.KanComplex C.obj` as a groupoid witness for arbitrary quasicategories;
- `PUnit`, `True`, or strict equality as fake equivalence-edge semantics;
- strict isomorphism of quasicategories as the definition of `CatEquiv`;
- ordinary homotopy-category localization as the SCT localization;
- a separate primitive fixed-endpoint hom anima when it can be derived from `mapAnima` and
  endpoint fibers.

## Acceptance checks for a serious implementation

A completed implementation should provide:

1. `Map(C,D)` as a Kan complex whose underlying category maps to `Fun(C,D)`;
2. `core(C)` identified with `Map(*,C)`;
3. object/morphism collections using cores rather than fake groupoid witnesses;
4. a universal property for maps from anima/groupoids into `C`;
5. a derived fixed-endpoint hom-anima API compatible with `objectHomCat`;
6. no new untracked semantic assumptions hidden in `Model.lean`.
