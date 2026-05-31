# SCT tutorial and exercises

This tutorial introduces the Synthetic Category Theory (SCT) experiment in this repository and the
InternalLean syntax used to implement it.

SCT is an active research implementation of the type theory from the Cisinski--Cnossen--Nguyen--
Walde Synthetic Category Theory book project. The files are meant to track the book closely, but the
interface is not stable. Some declarations are still admitted, the quasicategory model is a
skeleton, and several current witness fields are expected to change as the formalization matures.

A good way to use this tutorial is to open `InternalMath/SCT/TutorialExercises.lean` in your editor
and replace the exercise `sorry`s. You can also use a scratch Lean file that imports
`InternalMath.SCT.Spec`. Scratch files may contain temporary `sorry`s while you work. Avoid adding
exercise admissions to the core SCT modules unless you intend them to become part of the project.

## 1. The two languages in one file

SCT files are Lean files, but most declarations inside `declare_type_theory`,
`extend_type_theory`, `lf_def`, and `internal def` are written in InternalLean's object language.
For example:

```lean
declare_type_theory SCT{u} where
  syntax_sort Anima : Type (u+1)
  syntax_sort SCat : Type (u+1)
  lf_opaque animaCat (A : Anima) : SCat
```

The names `Anima` and `SCat` are syntax sorts in the object theory `SCT`. InternalLean then
generates Lean-facing metadata and, later, model-interface obligations for these declarations.

The main SCT entry points are:

- `InternalMath/SCT/Spec.lean`: stable aggregate import for the SCT specification;
- `InternalMath/SCT/Spec/Prelude.lean`: initial `declare_type_theory SCT{u}` block;
- `InternalMath/SCT/Spec/Chapter*/...`: staged `extend_type_theory SCT where` blocks;
- `InternalMath/SCT/Model.lean`: generated `SCTModel` interface and current quasicategory model
  skeleton.

## 2. Basic InternalLean declarations used by SCT

### `declare_type_theory` and `extend_type_theory`

`declare_type_theory` starts a new object theory. SCT is declared once in
`Spec/Prelude.lean`:

```lean
declare_type_theory SCT{u} where
  ...
```

The `{u}` is an InternalLean universe parameter for the object theory. Later files reopen the same
theory:

```lean
extend_type_theory SCT where
  model_section Chapter3
  ...
```

Use `extend_type_theory` when adding new SCT vocabulary or checked LF definitions. Use the stable
aggregate import `InternalMath.SCT.Spec` when you only want to work with the existing theory.

### `model_section`

`model_section Chapter3` groups subsequent model obligations. It has no mathematical content by
itself. It makes generated model templates easier to navigate.

### `syntax_sort`

A `syntax_sort` is an object-language family of terms or data:

```lean
syntax_sort Functor (C : SCat) (D : SCat) : Type u
syntax_sort CatEquiv (C : SCat) (D : SCat) : Type u
```

The result universe controls the Lean universe of the corresponding model field. In SCT,
`SCat : Type (u+1)` and `Functor C D : Type u` reflect the intended quasicategory semantics: small
synthetic categories live one universe above their mapping types.

### `syntax_sort_role`

A role is metadata for tools. It adds no constructors, theorems, or model laws.

```lean
syntax_sort ObjectwiseNatIsoData ... : Type u
syntax_sort_role ObjectwiseNatIsoData : side_structure
```

SCT uses `side_structure` for proof-like or property-like data that is still represented as a
syntax sort. Examples include `ObjectwiseNatIsoData`, `InvertibleMorphismData`, and several current
subcategory witness sorts.

### `judgment` and `judgment_role`

A `judgment` declares an object-theory proposition or relation. SCT has few custom judgments because
most mathematical data is represented intrinsically by syntax sorts. One important example is:

```lean
judgment isAnimaCat (C : SCat)
judgment_role isAnimaCat : side_judgment
```

`side_judgment` is a role tag used with `judgment_role`. The spelling is `judgment_role ... :
side_judgment`. A side judgment records a property outside the carrier sort itself. Here it says
that a synthetic category is an anima-category.

### `rule`

A `rule` is an inference rule for a judgment:

```lean
rule anima_cat_is_anima (A : Anima) where
  conclusion : isAnimaCat (animaCat A)
```

Rules are checked as object-theory rules. They are not Lean theorems, although InternalLean can
transport checked internal rules and definitions to generated model interfaces.

### `syntax_abbrev`

A `syntax_abbrev` is notation that expands before checking and model-obligation generation:

```lean
syntax_abbrev Obj (C : SCat) := Functor terminalCat C

syntax_abbrev NatIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D) :=
  Σ natIsoTrans : NatTrans C D F G, ObjectwiseNatIso C D F G natIsoTrans
```

`Obj C` means a functor from the terminal category into `C`. `NatIso` is currently represented as a
Sigma package consisting of an underlying natural transformation plus objectwise invertibility
evidence.

### `lf_opaque`

`lf_opaque` introduces primitive vocabulary or axiom data:

```lean
lf_opaque idFunctor (C : SCat) : Functor C C
lf_opaque terminalCat : SCat
```

Typed `lf_opaque` declarations usually become model-interface fields unless they are hidden or
replaced by checked definitions. Do not use `lf_opaque` merely to hide a theorem that should be
proved internally.

### `lf_def`

`lf_def` is a checked LF definition inside a theory block:

```lean
lf_def coreInclEmbedding : (C : SCat) ⇒ Embedding (coreCat C) C (coreIncl C) :=
  fun C => fst (coreUniversalPackage C)
```

Use `lf_def` when a declaration is definitional from previous SCT data. It unfolds during internal
conversion and normally should not add a new model obligation.

### `internal def`, `internal theorem`, and `internal_defs`

After a theory exists, you can add checked internal declarations from the Lean namespace of the
theory:

```lean
namespace SCT

internal def example (A : Anima) : isAnimaCat (animaCat A) := by
  exact anima_cat_is_anima A

end SCT
```

`internal_defs where` batches several declarations in source order. SCT uses it for
currently-admitted theorem debt:

```lean
namespace SCT

internal_defs where
  def someFutureTheorem : SomeStatement := sorry

end SCT
```

For theorem-shaped debt, prefer `internal theorem ... := sorry` or a clearly documented
`internal_defs` admission. Such admissions remain visible to `#lint_type_theory_sorries SCT` and do
not silently become model-provider fields.

## 3. Reading SCT declarations

SCT is intrinsic: most sorts contain valid data by construction. There is no global wellformedness
judgment for every object. Instead, the declaration uses:

- syntax sorts for objects, categories, functors, equivalences, fibrations, and witness data;
- side judgments for occasional properties such as `isAnimaCat`;
- Sigma packages for explicit data with projections;
- `lf_opaque` for primitive vocabulary and book axiom data;
- `lf_def` and internal definitions for constructions and theorems derived from earlier data.

For example, the object type of a category is defined by abbreviation:

```lean
Obj C := Functor terminalCat C
```

A point of `C` is a functor from the terminal category into `C`.

Likewise, an anima subobject is represented by an anima, an inclusion functor, and embedding
evidence:

```lean
AnimaSubobject A :=
  Σ B : Anima,
    Σ incl : Functor (animaCat B) (animaCat A),
      Embedding (animaCat B) (animaCat A) incl
```

This style makes the SCT API categorical rather than elementwise.

## 4. Working internally in SCT

Create a scratch file with:

```lean
import InternalMath.SCT.Spec

namespace SCT

-- exercises go here

end SCT
```

The following exercises are small enough to solve by reading `Spec/Prelude.lean` and
`Spec/Chapter1/BasicConstructions.lean`.

### Exercise 1: use a judgment rule

Fill the proof using the rule `anima_cat_is_anima`.

```lean
internal def exercise01_anima_cat (A : Anima) : isAnimaCat (animaCat A) := by
  sorry
```

Expected idea:

```lean
exact anima_cat_is_anima A
```

### Exercise 2: use a rule with parameters

Use `equiv_to_anima_is_anima`.

```lean
internal def exercise02_equiv_to_anima
    (C : SCat) (A : Anima) (e : CatEquiv C (animaCat A)) : isAnimaCat C := by
  sorry
```

### Exercise 3: remember what `Obj C` means

`Obj C` expands to `Functor terminalCat C`. Fill the definition with the parameter already in the
context.

```lean
internal def exercise03_object_as_functor (C : SCat) (x : Obj C) : Functor terminalCat C := by
  sorry
```

### Exercise 4: add a checked LF alias

Some object-level definitions are most predictable as `lf_def`s in an extension block. Try to write
an alias for the right unitor in a scratch file outside the `namespace SCT` block. The finished
block should look like this:

```lean
@[expose] public section

extend_type_theory SCT where
  lf_def exercise04_right_unitor_alias :
      (C : SCat) ⇒ (D : SCat) ⇒ (F : Functor C D) ⇒
        NatIso C D (compFunctor C D D F (idFunctor D)) F :=
    fun C D F => rightUnitor C D F
```

### Exercise 5: inspect the theory

Add these commands to a scratch file and read the messages in your editor:

```lean
#check_theory SCT
#print_type_theory_anchor SCT
#lint_type_theory_sorries SCT
#check_model_obligations SCT
```

The current `#lint_type_theory_sorries SCT` output is expected to list admitted internal
SCT declarations. Your scratch exercises can add more admissions locally if they still contain
`sorry`.

### Exercise 6: find a projection package

Open `InternalMath/SCT/Spec/Chapter2/Cores.lean` and find `coreUniversalPackage`. Then find the
checked projections `coreInclEmbedding`, `coreLiftPackage`, `coreLift`, `coreLiftBeta`, and
`coreLiftUniq`.

Questions:

1. Which projection is just `fst (coreUniversalPackage C)`?
2. Which projections come from nested `snd`s?
3. Why is this better than five unrelated primitive fields?

### Exercise 7: distinguish primitive data from theorem debt

Open `InternalMath/SCT/Spec/Chapter6/StrongSurjectivity.lean`. Find:

- the definition of `StronglySurjective`;
- `stronglySurjectivePreimage`;
- `stronglySurjectiveBeta`.

Questions:

1. Which declaration is the definition from the book?
2. Which declarations are currently admitted internal consequences?
3. What data in `StronglySurjective` should eventually be used to prove the admitted declarations?

## 5. Current design debt: subcategories and side structures

The implementation is experimental, and some fields are expected to change. The clearest current
example is the Chapter 3 subcategory and full-subcategory interface.

Today, several notions are primitive side structures:

```lean
LandsInObjectCollection
containsIdentities
closedUnderComposition
PreservesMorphismCollection
```

They are marked with:

```lean
syntax_sort_role ... : side_structure
```

This is useful for staging the book interface, but it lacks the data needed for all expected
internal proofs. For example, to prove that a functor preserving endpoint membership preserves the
full-subcategory morphism collection, the proof should be able to unpack concrete factorization
data. A forthcoming public design note will explain this in detail.

The likely direction is to replace some primitive side structures by explicit definitions or
packages. For instance, `LandsInObjectCollection D C P F` should expose that the induced map on
cores factors through the object-collection inclusion:

```text
coreCat D  --coreFunctor D C F-->  coreCat C
    \                                 ↑
     \                                |
      ------> objectCollectionCat C P --objectCollectionIncl C P--
```

Similarly, `PreservesMorphismCollection D C W F` should expose that the arrow-action map induced by
`F` factors through the selected morphism collection `W`.

This kind of change determines which consequences can be proved internally without adding new
opaque fields. When working on SCT, ask:

1. Is this declaration primitive vocabulary from the book?
2. Is it book axiom data?
3. Is it a definition that should be an `lf_def` or checked internal definition?
4. Is it a theorem that should remain visible as theorem debt until proved?

## 6. Common pitfalls

### Do not confuse Lean equality with SCT equivalence

SCT uses `NatIso`, `CatEquiv`, pullback universal properties, and related categorical data. Avoid
replacing these with Lean equality unless the statement is genuinely definitional.

### Do not hide theorem debt in model fields

If a book theorem is currently hard to prove, leave it as visible internal debt or improve the
representation. Do not turn it into `lf_opaque` unless the book treats it as primitive axiom data.

### Remember that role declarations are metadata

`judgment_role isAnimaCat : side_judgment` and `syntax_sort_role X : side_structure` help tools
classify declarations. They do not create constructors or proofs.

### Prefer the aggregate import for users

Use:

```lean
import InternalMath.SCT.Spec
```

for normal internal SCT work. Import split chapter files only when you are editing that part of the
specification or trying to keep a file very narrow.

## 7. Further reading

- `Docs/SCT.md`: current SCT status and expected warnings.
- `Docs/STLC.md`: the complete InternalLean example in this repository.
- `.lake/packages/InternalLean/Docs/UserGuide.md`: InternalLean workflow.
- `.lake/packages/InternalLean/Docs/Syntax.md`: full frontend syntax reference.
- `.lake/packages/InternalLean/Examples/IntroExercises.lean`: small standalone InternalLean
  exercises.
