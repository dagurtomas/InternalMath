# SCT tutorial and exercises

This tutorial introduces the Synthetic Category Theory (SCT) experiment and the InternalLean syntax
used to implement it.

SCT is a work-in-progress implementation of the type theory from the
Cisinski--Cnossen--Nguyen--Walde **Synthetic Category Theory** book project. The specification
tracks the book's vocabulary. The quasicategory model skeleton and several theorem proofs are
visible development targets.

For hands-on practice, open `InternalMath/SCT/TutorialExercises.lean` in your editor and replace the
exercise `sorry`s. You can also make a scratch file that imports `InternalMath.SCT.Spec`.

## 1. Lean and InternalLean

SCT files are Lean files. Inside `declare_type_theory`, `extend_type_theory`, `lf_def`, and
`internal def`, the declarations are written in InternalLean.

A first SCT block looks like this:

```lean
declare_type_theory SCT{u} where
  syntax_sort Anima : Type (u+1)
  syntax_sort SCat : Type (u+1)
  lf_opaque animaCat (A : Anima) : SCat
```

Here `Anima` and `SCat` are sorts in the type theory `SCT`. InternalLean records this theory and
can generate Lean model obligations from it.

The main files are:

- `InternalMath/SCT/Spec.lean`: stable aggregate import for the SCT specification;
- `InternalMath/SCT/Spec/Prelude.lean`: the initial `declare_type_theory SCT{u}` block;
- `InternalMath/SCT/Spec/Chapter*/...`: staged extensions of the theory;
- `InternalMath/SCT/Model.lean`: the generated `SCTModel` interface and model skeleton;
- `InternalMath/SCT/IML/Model/`: workshop project files for SCT model construction.

## 2. Common SCT declaration forms

### `declare_type_theory` and `extend_type_theory`

`declare_type_theory` starts a new type theory:

```lean
declare_type_theory SCT{u} where
  ...
```

The `{u}` is an InternalLean universe parameter. Later files add declarations with:

```lean
extend_type_theory SCT where
  model_section Chapter3
  ...
```

Use `import InternalMath.SCT.Spec` when you only need the finished SCT specification.

### `model_section`

`model_section Chapter3` groups generated model obligations. It is an organizational marker.

### `syntax_sort`

A `syntax_sort` declares a family of primitive data:

```lean
syntax_sort Functor (C : SCat) (D : SCat) : Type u
syntax_sort CatEquiv (C : SCat) (D : SCat) : Type u
```

The result universe controls the Lean universe of the corresponding model field. In SCT,
`SCat : Type (u+1)` and `Functor C D : Type u` match the intended quasicategory semantics.

### `syntax_def`

A `syntax_def` declares a derived family. The body may be a checked package or an admitted package
with projection/theorem debt:

```lean
syntax_def containsIdentities (C : SCat) (W : MorphismCollection C) : Type u := sorry
```

Admitted `syntax_def`s are lint-visible source debt. They do not become model-provider fields.

### `syntax_sort_role`

A role is metadata for tools. Despite the command name, SCT also uses it for `syntax_def` packages:

```lean
syntax_sort_role containsIdentities : side_structure
```

It does not add constructors, proofs, or equations.

### `judgment`, `judgment_role`, and `rule`

A `judgment` declares a type-theoretic judgment:

```lean
judgment isAnimaCat (C : SCat)
judgment_role isAnimaCat : side_judgment
```

A `rule` declares an inference rule whose conclusion is a `judgment`:

```lean
rule anima_cat_is_anima (A : Anima) where
  conclusion : isAnimaCat (animaCat A)
```

### `syntax_abbrev`

A `syntax_abbrev` is notation that expands before checking:

```lean
syntax_abbrev Obj (C : SCat) := Functor terminalCat C

syntax_abbrev NatIso (C : SCat) (D : SCat) (F : Functor C D) (G : Functor C D) :=
  Σ natIsoTrans : NatTrans C D F G, ObjectwiseNatIso C D F G natIsoTrans
```

Thus `Obj C` means a functor from the terminal category into `C`.

### `lf_opaque`

`lf_opaque` introduces primitive vocabulary or axiom data:

```lean
lf_opaque idFunctor (C : SCat) : Functor C C
lf_opaque terminalCat : SCat
```

Typed `lf_opaque` declarations become fields in the generated model interface.

### `lf_def`

`lf_def` is a checked definition inside a theory block:

```lean
lf_def coreInclEmbedding : (C : SCat) ⇒ Embedding (coreCat C) C (coreIncl C) :=
  fun C => fst (coreUniversalPackage C)
```

Use it when a construction is definable from earlier SCT data.

### `internal def`, `internal theorem`, and `internal_defs`

After the theory exists, you can add checked internal declarations from the Lean namespace `SCT`:

```lean
namespace SCT

internal def example (A : Anima) : isAnimaCat (animaCat A) := by
  exact anima_cat_is_anima A

end SCT
```

`internal_defs where` batches several declarations in source order. Admissions in internal
statements remain visible to `#lint_type_theory_sorries SCT`.

## 3. Reading SCT declarations

SCT is intrinsic: most sorts contain valid data by construction. There is no separate
well-formedness judgment. The specification uses:

- syntax sorts for categories, functors, equivalences, fibrations, and witness data;
- side judgments for occasional properties such as `isAnimaCat`;
- Sigma packages for data with projections;
- `lf_opaque` for primitive vocabulary and book axiom data;
- `lf_def` and internal definitions for derived constructions.

For example:

```lean
Obj C := Functor terminalCat C
```

A point of `C` is a functor from the terminal category into `C`.

Likewise, an anima subobject is represented by an anima, an inclusion functor, and embedding data:

```lean
AnimaSubobject A :=
  Σ B : Anima,
    Σ incl : Functor (animaCat B) (animaCat A),
      Embedding (animaCat B) (animaCat A) incl
```

## 4. Exercises

Create a scratch file with:

```lean
import InternalMath.SCT.Spec

namespace SCT

-- exercises go here

end SCT
```

The first exercises can be solved by reading `Spec/Prelude.lean` and
`Spec/Chapter1/BasicConstructions.lean`.

### Exercise 1: use a judgment rule

Fill the proof using `anima_cat_is_anima`.

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

`Obj C` expands to `Functor terminalCat C`.

```lean
internal def exercise03_object_as_functor (C : SCat) (x : Obj C) : Functor terminalCat C := by
  sorry
```

### Exercise 4: add a checked LF alias

Some internal definitions are convenient as `lf_def`s in an extension block. Outside the
`namespace SCT` block, try this alias for the right unitor:

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

The linter lists admitted SCT declarations. That is expected for this experiment.

### Exercise 6: find a projection package

Open `InternalMath/SCT/Spec/Chapter2/Cores.lean` and find `coreUniversalPackage`. Then find
`coreInclEmbedding`, `coreLiftPackage`, `coreLift`, `coreLiftBeta`, and `coreLiftUniq`.

Questions:

1. Which projection is `fst (coreUniversalPackage C)`?
2. Which projections come from nested `snd`s?
3. Why is one package better than five unrelated primitive fields?

### Exercise 7: distinguish definitions from theorem debt

Open `InternalMath/SCT/Spec/Chapter6/StrongSurjectivity.lean`. Find:

- the definition of `StronglySurjective`;
- `stronglySurjectivePreimage`;
- `stronglySurjectiveBeta`.

Questions:

1. Which declaration is the definition from the book?
2. Which declarations are admitted consequences?
3. What data in `StronglySurjective` should eventually prove them?

## 5. Project status

The SCT specification includes admitted internal declarations for theorem and projection debt.
Several Chapter 3 subcategory notions are admitted `syntax_def` packages whose checked constructors
and projections are workshop targets. The model file contains placeholder obligations for the
quasicategory interpretation.

These gaps are kept visible so that the specification, internal proofs, and model obligations can
converge on the book's formulation.

## 6. Common distinctions

### Lean equality and SCT equivalence

SCT uses categorical data such as `NatIso`, `CatEquiv`, and pullback universal properties. Lean
equality only applies when a statement is definitional.

### Primitive data and derived facts

Use `lf_opaque` for primitive vocabulary and axiom data. Use `lf_def` or checked internal
definitions for constructions derived from earlier declarations.

### Roles and data

`judgment_role` and `syntax_sort_role` classify declarations for tools. They do not provide data on
their own.

### Aggregate import

For normal SCT work, import:

```lean
import InternalMath.SCT.Spec
```

Import a split chapter file only when you are editing that part of the specification.

## 7. Further reading

- `Docs/SCT.md`: SCT status and expected warnings.
- `Docs/STLC.md`: the complete InternalLean example in this repository.
- `.lake/packages/InternalLean/Docs/UserGuide.md`: InternalLean workflow.
- `.lake/packages/InternalLean/Docs/Syntax.md`: full frontend syntax reference.
- `.lake/packages/InternalLean/Examples/IntroExercises.lean`: small standalone InternalLean
  exercises.
