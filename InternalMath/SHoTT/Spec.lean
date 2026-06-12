/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalLean.Command

/-!
# Simplicial homotopy type theory

This file declares an intrinsic LF skeleton for Riehl--Shulman simplicial homotopy type
theory.  Contexts, cubes, topes, ordinary types, and terms are represented by dependent
syntax sorts, so external formation and typing judgments are absent.  Object-theory
propositions remain as judgments, with first-class evidence sorts where term constructors
need to consume a side condition.

The declaration is a research skeleton rather than a complete encoding of the paper.  It keeps the
three-layer structure used by sHoTT/Rzk, the strict interval and tope calculus, ordinary HoTT
constructors needed by the paper, disjunctive gluing, and dependent extension types.  The notes
under `Plans/SHoTTResearch/` track paper faithfulness and the remaining gaps.

This file also serves as a specification-debt map.  The seven internal admissions near the end are
only the checked placeholders.  A complete theory specification still needs more object-theory
structure before any semantic interpretation is considered:

* a general structural calculus for cube substitutions, tope restrictions, ordinary substitutions,
  and their coherence laws;
* first-class proof/evidence constructors for entailment, shape inclusion, and conversion evidence,
  not just bridge rules from evidence to judgments;
* properly guarded conversion and substitution operations, so casts and point substitutions consume
  the equality or membership evidence that the paper requires;
* full ordinary HoTT rules with dependent eliminators, η/computation principles, equivalences,
  function extensionality, and universe discipline;
* the complete extension-type rule package, including pointwise substitution and boundary
  computation;
* definitions of hom types, Segal conditions, Rezk completeness, covariance, and the derived
  simplicial constructions as object-theory data.
-/

@[expose] public section

/-- Intrinsic cube layer: cube contexts, cubes, cube terms, and strict cube-term equality. -/
/-
Specification gaps in the cube layer:

* Cubes are presented by `unit`, binary products, and the interval introduced later.  The paper uses
  finite cube contexts and substitutions between them.  A fuller signature should expose general
  cube substitutions/renamings and prove identity, composition, weakening, and substitution laws.
* `eqCubeTm` has product β/η and equivalence rules, but the layer lacks congruence for every later
  operation that consumes cube terms.  The later tope/type/term substitution declarations should be
  functorial for this equality.
* Variables are represented by `CubeVar`; the complete specification should say whether variables
  are de Bruijn-style structural artifacts or part of the object grammar, and should include the
  expected weakening/substitution equations for them.
-/
declare_type_theory CubeLayer where
  syntax_sort CubeCtx
  syntax_sort Cube
  syntax_sort CubeTm (Ξ : CubeCtx) (I : Cube)
  syntax_sort CubeVar (Ξ : CubeCtx) (I : Cube)

  syntax_sort_role CubeCtx : context
  syntax_sort_role Cube : cube_sort
  syntax_sort_role CubeTm : cube_term_sort

  context_zone cube : CubeCtx
  binder_class cube_var_binder : CubeTm in cube

  judgment eqCubeTm (Ξ : CubeCtx) (I : Cube) (s : CubeTm Ξ I) (t : CubeTm Ξ I)
  judgment_role eqCubeTm : term_conversion

  lf_opaque emptyCubeCtx : CubeCtx
  lf_opaque unit : Cube
  lf_opaque prod (I : Cube) (J : Cube) : Cube
  lf_opaque star (Ξ : CubeCtx) : CubeTm Ξ unit
  lf_opaque extendCubeCtx (Ξ : CubeCtx) (I : Cube) : CubeCtx
  lf_opaque cubeVarTerm {Ξ : CubeCtx} {I : Cube} (x : CubeVar Ξ I) : CubeTm Ξ I
  lf_opaque lastCubeVar {Ξ : CubeCtx} {I : Cube} : CubeVar (extendCubeCtx Ξ I) I
  lf_opaque weakenCubeVar {Ξ : CubeCtx} {I : Cube} (J : Cube) (x : CubeVar Ξ I) :
    CubeVar (extendCubeCtx Ξ J) I
  lf_opaque prodMk {Ξ : CubeCtx} {I : Cube} {J : Cube}
    (i : CubeTm Ξ I) (j : CubeTm Ξ J) : CubeTm Ξ (prod I J)
  lf_opaque pi1 {Ξ : CubeCtx} {I : Cube} {J : Cube} (x : CubeTm Ξ (prod I J)) :
    CubeTm Ξ I
  lf_opaque pi2 {Ξ : CubeCtx} {I : Cube} {J : Cube} (x : CubeTm Ξ (prod I J)) :
    CubeTm Ξ J

  rule eqCube_refl (Ξ : CubeCtx) (I : Cube) (t : CubeTm Ξ I) where
    conclusion : eqCubeTm Ξ I t t
  rule eqCube_sym (Ξ : CubeCtx) (I : Cube) (s : CubeTm Ξ I) (t : CubeTm Ξ I) where
    premise eqp : eqCubeTm Ξ I s t
    conclusion : eqCubeTm Ξ I t s
  rule eqCube_trans (Ξ : CubeCtx) (I : Cube)
      (r : CubeTm Ξ I) (s : CubeTm Ξ I) (t : CubeTm Ξ I) where
    premise left : eqCubeTm Ξ I r s
    premise right : eqCubeTm Ξ I s t
    conclusion : eqCubeTm Ξ I r t
  rule eqCube_prod_congr (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (i : CubeTm Ξ I) (i' : CubeTm Ξ I) (j : CubeTm Ξ J) (j' : CubeTm Ξ J) where
    premise left : eqCubeTm Ξ I i i'
    premise right : eqCubeTm Ξ J j j'
    conclusion : eqCubeTm Ξ (prod I J) (prodMk i j) (prodMk i' j')
  rule eqCube_pi1_congr (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (p : CubeTm Ξ (prod I J)) (q : CubeTm Ξ (prod I J)) where
    premise eqp : eqCubeTm Ξ (prod I J) p q
    conclusion : eqCubeTm Ξ I (pi1 p) (pi1 q)
  rule eqCube_pi2_congr (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (p : CubeTm Ξ (prod I J)) (q : CubeTm Ξ (prod I J)) where
    premise eqp : eqCubeTm Ξ (prod I J) p q
    conclusion : eqCubeTm Ξ J (pi2 p) (pi2 q)
  rule eqCube_prod_beta_left (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (i : CubeTm Ξ I) (j : CubeTm Ξ J) where
    conclusion : eqCubeTm Ξ I (pi1 (prodMk i j)) i
  rule eqCube_prod_beta_right (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (i : CubeTm Ξ I) (j : CubeTm Ξ J) where
    conclusion : eqCubeTm Ξ J (pi2 (prodMk i j)) j
  rule eqCube_prod_eta (Ξ : CubeCtx) (I : Cube) (J : Cube)
      (p : CubeTm Ξ (prod I J)) where
    conclusion : eqCubeTm Ξ (prod I J) (prodMk (pi1 p) (pi2 p)) p
  rule eqCube_unit_eta (Ξ : CubeCtx) (t : CubeTm Ξ unit) where
    conclusion : eqCubeTm Ξ unit t (star Ξ)

/-- Intrinsic tope layer: tope contexts, topes, and entailment. -/
/-
Specification gaps in the tope layer:

* The paper's tope calculus is a logic of constraints over cube variables.  This skeleton has the
  connectives and basic entailment rules, but it still needs a proper cut/substitution theorem for
  entailment and explicit stability under cube substitution.
* `EntailsEvidence` is a first-class side-condition sort, but only the bridge from evidence to the
  judgment is declared.  To use evidence without admissions, the signature needs constructors or
  checked internal definitions mirroring the entailment rules below.
* Equality topes should support replacement throughout topes, types, terms, and evidence.  The
  later `substTyTopeEq` and `substTmTopeEq` declarations cover only a small part of this.
* Disjunction in the tope layer should connect to term-level gluing.  Entailment elimination for
  `φ ∨ ψ` is present, but term computation over disjunctive tope contexts is incomplete below.
-/
declare_type_theory TopeLayer extends CubeLayer where
  syntax_sort TopeCtx (Ξ : CubeCtx)
  syntax_sort Tope (Ξ : CubeCtx)
  syntax_sort TopeHyp (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ)

  syntax_sort_role TopeCtx : context
  syntax_sort_role Tope : tope_sort

  context_zone tope : TopeCtx depends_on cube
  binder_class tope_assumption_binder : Tope in tope depends_on cube

  judgment entails (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ)
  judgment_role entails : side_judgment
  /-- First-class evidence for tope entailment, used when a term constructor must consume the
  entailment as an argument rather than merely produce a judgment.
  -/
  syntax_sort EntailsEvidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ)
  syntax_sort_role EntailsEvidence : side_structure

  rule entails_of_evidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ)
      (p : EntailsEvidence Ξ Φ φ) where
    conclusion : entails Ξ Φ φ

  lf_opaque emptyTopeCtx (Ξ : CubeCtx) : TopeCtx Ξ
  lf_opaque extendTopeCtx (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) : TopeCtx Ξ
  lf_opaque lastTopeHyp (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) :
    TopeHyp Ξ (extendTopeCtx Ξ Φ φ) φ
  lf_opaque weakenTopeHyp (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ)
    (h : TopeHyp Ξ Φ φ) : TopeHyp Ξ (extendTopeCtx Ξ Φ ψ) φ

  lf_opaque top {Ξ : CubeCtx} : Tope Ξ
  lf_opaque bottom {Ξ : CubeCtx} : Tope Ξ
  lf_opaque topeAnd {Ξ : CubeCtx} (φ : Tope Ξ) (ψ : Tope Ξ) : Tope Ξ
  lf_opaque topeOr {Ξ : CubeCtx} (φ : Tope Ξ) (ψ : Tope Ξ) : Tope Ξ
  lf_opaque topeEq {Ξ : CubeCtx} {I : Cube} (s : CubeTm Ξ I) (t : CubeTm Ξ I) :
    Tope Ξ

  rule entails_top (Ξ : CubeCtx) (Φ : TopeCtx Ξ) where
    conclusion : entails Ξ Φ top
  rule entails_bottom_elim (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) where
    premise absurd : entails Ξ Φ bottom
    conclusion : entails Ξ Φ φ
  rule entails_and_intro (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise left : entails Ξ Φ φ
    premise right : entails Ξ Φ ψ
    conclusion : entails Ξ Φ (topeAnd Ξ φ ψ)
  rule entails_and_left (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise both : entails Ξ Φ (topeAnd Ξ φ ψ)
    conclusion : entails Ξ Φ φ
  rule entails_and_right (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise both : entails Ξ Φ (topeAnd Ξ φ ψ)
    conclusion : entails Ξ Φ ψ
  rule entails_or_left_intro (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise left : entails Ξ Φ φ
    conclusion : entails Ξ Φ (topeOr Ξ φ ψ)
  rule entails_or_right_intro (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise right : entails Ξ Φ ψ
    conclusion : entails Ξ Φ (topeOr Ξ φ ψ)
  rule entails_or_elim (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (φ : Tope Ξ) (ψ : Tope Ξ) (χ : Tope Ξ) where
    premise split : entails Ξ Φ (topeOr Ξ φ ψ)
    premise left : entails Ξ (extendTopeCtx Ξ Φ φ) χ
    premise right : entails Ξ (extendTopeCtx Ξ Φ ψ) χ
    conclusion : entails Ξ Φ χ
  rule entails_weaken (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ) (ψ : Tope Ξ) where
    premise proof : entails Ξ Φ φ
    conclusion : entails Ξ (extendTopeCtx Ξ Φ ψ) φ
  rule entails_eq_refl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (I : Cube) (t : CubeTm Ξ I) where
    conclusion : entails Ξ Φ (topeEq Ξ I t t)
  rule entails_eq_sym (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (I : Cube)
      (s : CubeTm Ξ I) (t : CubeTm Ξ I) where
    premise eqp : entails Ξ Φ (topeEq Ξ I s t)
    conclusion : entails Ξ Φ (topeEq Ξ I t s)
  rule entails_eq_trans (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (I : Cube)
      (r : CubeTm Ξ I) (s : CubeTm Ξ I) (t : CubeTm Ξ I) where
    premise left : entails Ξ Φ (topeEq Ξ I r s)
    premise right : entails Ξ Φ (topeEq Ξ I s t)
    conclusion : entails Ξ Φ (topeEq Ξ I r t)
  rule entails_eq_of_cube_eq (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (I : Cube)
      (s : CubeTm Ξ I) (t : CubeTm Ξ I) where
    premise eqp : eqCubeTm Ξ I s t
    conclusion : entails Ξ Φ (topeEq Ξ I s t)
  rule tope_assumption (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (φ : Tope Ξ)
      (h : TopeHyp Ξ Φ φ) where
    conclusion : entails Ξ Φ φ
  rule_role tope_assumption : structural

/- Core sHoTT logical-framework signature. -/
/-
Specification gaps at the start of the ordinary layer:

* `Shape` is still a primitive sort.  The intended package is close to
  `Σ I : Cube, Tope (extendCubeCtx Ξ I)`, with appropriate equality or presentation rules.  Making
  that package explicit would let shape inclusions compute from tope entailments more often.
* `TyCtx`, `Ty`, and `Tm` are intrinsic sorts, which is the desired architecture.  The missing part
  is the structural calculus: reindexing along cube substitutions, restriction along topes,
  ordinary substitution, and all coherence laws between these actions.
* `shapeIncl`, `eqType`, and `eqTerm` are judgments.  Constructors that consume such facts use the
  evidence sorts below, but the evidence layer still lacks enough constructors to avoid admitting
  ordinary side conditions.
-/
declare_type_theory SHoTT extends TopeLayer where
  syntax_sort Shape (Ξ : CubeCtx)
  syntax_sort TyCtx (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
  syntax_sort Ty (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
  syntax_sort Tm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (A : Ty Ξ Φ Γ)
  syntax_sort TyVar (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (A : Ty Ξ Φ Γ)

  syntax_sort_role Shape : shape_sort
  syntax_sort_role TyCtx : context
  syntax_sort_role Ty : type_sort
  syntax_sort_role Tm : term_sort
  syntax_sort_role TyVar : term_sort

  context_zone ordinary : TyCtx depends_on cube, tope
  binder_class ordinary_var_binder : Tm in ordinary depends_on cube, tope

  judgment shapeIncl (Ξ : CubeCtx) (S : Shape Ξ) (T : Shape Ξ)
  judgment eqType (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ)
  judgment eqTerm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A)

  judgment_role shapeIncl : side_judgment
  judgment_role eqType : type_conversion
  judgment_role eqTerm : term_conversion
  /-- First-class evidence for a shape inclusion.  This is used by extension types, whose
  formation depends on an inclusion `{t : I | φ} ⊆ {t : I | ψ}`.
  -/
  syntax_sort ShapeInclEvidence {Ξ : CubeCtx} (S : Shape Ξ) (T : Shape Ξ)
  syntax_sort_role ShapeInclEvidence : side_structure
  /-- First-class evidence for ordinary type conversion, for constructors that need a conversion
  as data.
  -/
  syntax_sort EqTypeEvidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ)
  syntax_sort_role EqTypeEvidence : side_structure
  /-- First-class evidence for ordinary term conversion, for constructors that need a conversion
  as data.
  -/
  syntax_sort EqTermEvidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A)
  syntax_sort_role EqTermEvidence : side_structure

  rule shape_incl_of_evidence {Ξ : CubeCtx} (S : Shape Ξ) (T : Shape Ξ)
      (p : ShapeInclEvidence S T) where
    conclusion : shapeIncl Ξ S T
  rule eqType_of_evidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (p : EqTypeEvidence Ξ Φ Γ A B) where
    conclusion : eqType Ξ Φ Γ A B
  rule eqTerm_of_evidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A)
      (p : EqTermEvidence Ξ Φ Γ A a b) where
    conclusion : eqTerm Ξ Φ Γ A a b

  /-
  Missing evidence constructors:

  The bridge rules above let first-class evidence produce judgments.  The reverse direction is not
  available in general, and none of the equivalence/congruence rules below produces first-class
  evidence.  For a complete specification, each theorem that term constructors need as data should
  either produce evidence directly or have a checked internal definition converting the
  corresponding judgment proof into evidence.  This matters for extension boundaries, branch
  overlaps, point membership, and future hom/Segal/Rezk side conditions.
  -/

  conversion_plugin shott_conversion

  /-- Directed interval and its order topes. -/
  /-
  Missing interval/tope specification:

  The interval rules below give a preorder with endpoints, totality, and antisymmetry, plus
  incompatibility of `0 = 1`.  A full paper-level presentation should also include the substitution
  and congruence principles needed to push `≤` and endpoint equations through cube products and
  shape presentations.  If additional interval algebra appears in the paper or Rzk rules, those
  laws should live here rather than inside low-dimensional special cases.
  -/
  lf_opaque interval : Cube
  lf_opaque zero {Ξ : CubeCtx} : CubeTm Ξ interval
  lf_opaque one {Ξ : CubeCtx} : CubeTm Ξ interval
  lf_opaque leq {Ξ : CubeCtx} (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) : Tope Ξ

  rule entails_leq_refl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (i : CubeTm Ξ interval) where
    conclusion : entails Ξ Φ (leq Ξ i i)
  rule entails_zero_leq (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (i : CubeTm Ξ interval) where
    conclusion : entails Ξ Φ (leq Ξ (zero Ξ) i)
  rule entails_leq_one (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (i : CubeTm Ξ interval) where
    conclusion : entails Ξ Φ (leq Ξ i (one Ξ))
  rule entails_leq_total (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) where
    conclusion : entails Ξ Φ (topeOr Ξ (leq Ξ i j) (leq Ξ j i))
  rule entails_zero_ne_one (Ξ : CubeCtx) (Φ : TopeCtx Ξ) where
    premise path : entails Ξ Φ (topeEq Ξ interval (zero Ξ) (one Ξ))
    conclusion : entails Ξ Φ bottom
  rule entails_leq_trans (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) (k : CubeTm Ξ interval) where
    premise left : entails Ξ Φ (leq Ξ i j)
    premise right : entails Ξ Φ (leq Ξ j k)
    conclusion : entails Ξ Φ (leq Ξ i k)
  rule entails_leq_eq_left (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) (k : CubeTm Ξ interval) where
    premise eqp : entails Ξ Φ (topeEq Ξ interval i j)
    premise order : entails Ξ Φ (leq Ξ j k)
    conclusion : entails Ξ Φ (leq Ξ i k)
  rule entails_leq_eq_right (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) (k : CubeTm Ξ interval) where
    premise eqp : entails Ξ Φ (topeEq Ξ interval i j)
    premise order : entails Ξ Φ (leq Ξ k i)
    conclusion : entails Ξ Φ (leq Ξ k j)
  rule entails_leq_antisym (Ξ : CubeCtx) (Φ : TopeCtx Ξ)
      (i : CubeTm Ξ interval) (j : CubeTm Ξ interval) where
    premise left : entails Ξ Φ (leq Ξ i j)
    premise right : entails Ξ Φ (leq j i)
    conclusion : entails Ξ Φ (topeEq Ξ interval i j)

  /-- Shapes are topes in a fresh cube variable; inclusions are induced by tope entailment. -/
  /-
  Missing shape calculus:

  `shapeOf I φ` is the intended presentation `{t : I | φ}`.  The specification still needs the
  general operations on shapes used by extension types and simplicial examples: pullback/reindexing
  of shapes along cube substitutions, equality or isomorphism of alternative presentations, unions
  and intersections when they are used by boundaries, and reusable face/horn inclusions.  Shape
  inclusion evidence should compose with all of these operations.
  -/
  lf_opaque shapeOf {Ξ : CubeCtx} (I : Cube) (φ : Tope (extendCubeCtx Ξ I)) : Shape Ξ
  rule shape_inclusion_refl (Ξ : CubeCtx) (S : Shape Ξ) where
    conclusion : shapeIncl Ξ S S
  rule shape_inclusion_trans (Ξ : CubeCtx) (R : Shape Ξ) (S : Shape Ξ) (T : Shape Ξ) where
    premise left : shapeIncl Ξ R S
    premise right : shapeIncl Ξ S T
    conclusion : shapeIncl Ξ R T
  rule shape_inclusion_of_entails (Ξ : CubeCtx) (I : Cube)
      (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I)) where
    premise incl : entails (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (emptyTopeCtx (extendCubeCtx Ξ I)) φ) ψ
    conclusion : shapeIncl Ξ (shapeOf I φ) (shapeOf I ψ)
  /-- First-class reflexive shape-inclusion evidence. -/
  lf_opaque shapeInclReflEvidence {Ξ : CubeCtx} (S : Shape Ξ) : ShapeInclEvidence S S
  /-- First-class transitive composition of shape-inclusion evidence. -/
  lf_opaque shapeInclTransEvidence {Ξ : CubeCtx} {R : Shape Ξ} {S : Shape Ξ} {T : Shape Ξ}
    (left : ShapeInclEvidence R S) (right : ShapeInclEvidence S T) : ShapeInclEvidence R T
  /-- First-class shape-inclusion evidence induced by an entailment between defining topes. -/
  lf_opaque shapeInclOfEntailsEvidence (Ξ : CubeCtx) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : EntailsEvidence (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (emptyTopeCtx (extendCubeCtx Ξ I)) φ) ψ) :
    ShapeInclEvidence (shapeOf I φ) (shapeOf I ψ)

  /-- Ordinary dependent type-theory contexts, structural operations, and conversions. -/
  /-
  Missing ordinary structural calculus:

  This block gives the first variables, weakening, single-variable substitution, and conversion
  judgments.  A complete dependent type theory specification needs multi-substitutions,
  substitution into contexts, variable β/η equations, weakening/substitution interchange,
  associativity, identity laws, and congruence for every type and term former.  These are required
  before the later hom and Segal definitions can be written without opaque casts.
  -/
  lf_opaque emptyTyCtx (Ξ : CubeCtx) (Φ : TopeCtx Ξ) : TyCtx Ξ Φ
  lf_opaque extendTyCtx (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) : TyCtx Ξ Φ
  lf_opaque weakenTy (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) : Ty Ξ Φ (extendTyCtx Ξ Φ Γ B)
  lf_opaque weakenTm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (B : Ty Ξ Φ Γ) :
      Tm Ξ Φ (extendTyCtx Ξ Φ Γ B) (weakenTy Ξ Φ Γ A B)
  lf_opaque tyVarTerm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (x : TyVar Ξ Φ Γ A) : Tm Ξ Φ Γ A
  lf_opaque lastTyVar (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) : TyVar Ξ Φ (extendTyCtx Ξ Φ Γ A) (weakenTy Ξ Φ Γ A A)
  lf_opaque weakenTyVar (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (x : TyVar Ξ Φ Γ A) :
      TyVar Ξ Φ (extendTyCtx Ξ Φ Γ B) (weakenTy Ξ Φ Γ A B)
  lf_opaque substTy (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A)) (a : Tm Ξ Φ Γ A) :
      Ty Ξ Φ Γ
  lf_opaque substTm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (b : Tm Ξ Φ (extendTyCtx Ξ Φ Γ A) B) (a : Tm Ξ Φ Γ A) :
      Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)
  /-
  Specification hole: `convTm` should be guarded by `eqType` or `EqTypeEvidence`.  As written it
  coerces a term of any type `A` to any type `B`.  It is kept as a marker for the conversion rule,
  but a complete signature should replace it with an evidence-indexed cast and propagate that
  evidence through all β/η rules that use conversion.
  -/
  lf_opaque convTm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) : Tm Ξ Φ Γ B

  rule subst_ty_congr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A) where
    premise term_eq : eqTerm Ξ Φ Γ A a b
    conclusion : eqType Ξ Φ Γ (substTy Ξ Φ Γ A B a) (substTy Ξ Φ Γ A B b)
  rule subst_ty_weaken (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (C : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) where
    conclusion : eqType Ξ Φ Γ (substTy Ξ Φ Γ A (weakenTy Ξ Φ Γ C A) a) C
  rule eqType_refl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (A : Ty Ξ Φ Γ) where
    conclusion : eqType Ξ Φ Γ A A
  rule eqType_sym (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) where
    premise eqp : eqType Ξ Φ Γ A B
    conclusion : eqType Ξ Φ Γ B A
  rule eqType_trans (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (C : Ty Ξ Φ Γ) where
    premise left : eqType Ξ Φ Γ A B
    premise right : eqType Ξ Φ Γ B C
    conclusion : eqType Ξ Φ Γ A C
  rule eqTerm_refl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) where
    conclusion : eqTerm Ξ Φ Γ A a a
  rule eqTerm_sym (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A) where
    premise eqp : eqTerm Ξ Φ Γ A a b
    conclusion : eqTerm Ξ Φ Γ A b a
  rule eqTerm_trans (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A) (c : Tm Ξ Φ Γ A) where
    premise left : eqTerm Ξ Φ Γ A a b
    premise right : eqTerm Ξ Φ Γ A b c
    conclusion : eqTerm Ξ Φ Γ A a c

  /-- Ordinary HoTT constructors used in the paper. -/
  /-
  Missing ordinary HoTT specification:

  The constructors below are enough to name many paper ingredients, but they are not a full HoTT
  theory.  The missing rules include dependent eliminators for coproducts and identity types,
  `Π` η and function extensionality, universe codes and decoding computation, congruence for all
  arguments of each type former, and a principled treatment of conversion.  `IsContr` should become
  a checked definition from `Σ`, `Π`, and `Id`, and the theory still needs equivalences and
  `IsEquiv` before Segal and Rezk conditions can be stated precisely.
  -/
  lf_opaque Uni (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) : Ty Ξ Φ Γ
  lf_opaque El (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Tm Ξ Φ Γ (Uni Ξ Φ Γ)) : Ty Ξ Φ Γ
  lf_opaque Pi (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A)) : Ty Ξ Φ Γ
  lf_opaque lam (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (b : Tm Ξ Φ (extendTyCtx Ξ Φ Γ A) B) : Tm Ξ Φ Γ (Pi Ξ Φ Γ A B)
  lf_opaque app (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (f : Tm Ξ Φ Γ (Pi Ξ Φ Γ A B)) (a : Tm Ξ Φ Γ A) :
      Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)
  rule pi_beta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (b : Tm Ξ Φ (extendTyCtx Ξ Φ Γ A) B) (a : Tm Ξ Φ Γ A) where
    conclusion : eqTerm Ξ Φ Γ (substTy Ξ Φ Γ A B a)
      (app Ξ Φ Γ A B (lam Ξ Φ Γ A B b) a) (substTm Ξ Φ Γ A B b a)
  rule pi_cod_congr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (C : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A)) where
    premise cod_eq : eqType Ξ Φ (extendTyCtx Ξ Φ Γ A) B C
    conclusion : eqType Ξ Φ Γ (Pi Ξ Φ Γ A B) (Pi Ξ Φ Γ A C)
  rule lam_congr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (b : Tm Ξ Φ (extendTyCtx Ξ Φ Γ A) B)
      (c : Tm Ξ Φ (extendTyCtx Ξ Φ Γ A) B) where
    premise body_eq : eqTerm Ξ Φ (extendTyCtx Ξ Φ Γ A) B b c
    conclusion : eqTerm Ξ Φ Γ (Pi Ξ Φ Γ A B)
      (lam Ξ Φ Γ A B b) (lam Ξ Φ Γ A B c)

  lf_opaque Sigma (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A)) : Ty Ξ Φ Γ
  lf_opaque pair (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)) :
      Tm Ξ Φ Γ (Sigma Ξ Φ Γ A B)
  lf_opaque «fst» (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (p : Tm Ξ Φ Γ (Sigma Ξ Φ Γ A B)) : Tm Ξ Φ Γ A
  lf_opaque «snd» (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (p : Tm Ξ Φ Γ (Sigma Ξ Φ Γ A B)) :
      Tm Ξ Φ Γ (substTy Ξ Φ Γ A B («fst» Ξ Φ Γ A B p))
  rule sigma_fst_beta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)) where
    conclusion : eqTerm Ξ Φ Γ A («fst» Ξ Φ Γ A B (pair Ξ Φ Γ A B a b)) a
  rule sigma_snd_beta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)) where
    conclusion : eqTerm Ξ Φ Γ
      (substTy Ξ Φ Γ A B («fst» Ξ Φ Γ A B (pair Ξ Φ Γ A B a b)))
      («snd» Ξ Φ Γ A B (pair Ξ Φ Γ A B a b))
      (convTm Ξ Φ Γ (substTy Ξ Φ Γ A B a)
        (substTy Ξ Φ Γ A B («fst» Ξ Φ Γ A B (pair Ξ Φ Γ A B a b))) b)
  rule sigma_eta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (p : Tm Ξ Φ Γ (Sigma Ξ Φ Γ A B)) where
    conclusion : eqTerm Ξ Φ Γ (Sigma Ξ Φ Γ A B)
      (pair Ξ Φ Γ A B («fst» Ξ Φ Γ A B p) («snd» Ξ Φ Γ A B p)) p

  /-
  Coproduct gap: `coprodElim` is non-dependent.  The paper uses disjunction-shaped computation in
  tope contexts, so the ordinary coproduct layer should eventually include dependent elimination,
  η/uniqueness, and interaction with tope restriction and `branchTm`.
  -/
  lf_opaque Coprod (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) : Ty Ξ Φ Γ
  lf_opaque inl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) :
      Tm Ξ Φ Γ (Coprod Ξ Φ Γ A B)
  lf_opaque inr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (b : Tm Ξ Φ Γ B) :
      Tm Ξ Φ Γ (Coprod Ξ Φ Γ A B)
  lf_opaque coprodElim (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (C : Ty Ξ Φ Γ)
    (f : Tm Ξ Φ Γ (Pi Ξ Φ Γ A (weakenTy Ξ Φ Γ C A)))
    (g : Tm Ξ Φ Γ (Pi Ξ Φ Γ B (weakenTy Ξ Φ Γ C B)))
    (s : Tm Ξ Φ Γ (Coprod Ξ Φ Γ A B)) : Tm Ξ Φ Γ C
  rule coprod_congr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (A' : Ty Ξ Φ Γ) (B' : Ty Ξ Φ Γ) where
    premise left_eq : eqType Ξ Φ Γ A A'
    premise right_eq : eqType Ξ Φ Γ B B'
    conclusion : eqType Ξ Φ Γ (Coprod Ξ Φ Γ A B) (Coprod Ξ Φ Γ A' B')
  rule coprod_beta_inl (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (C : Ty Ξ Φ Γ)
      (f : Tm Ξ Φ Γ (Pi Ξ Φ Γ A (weakenTy Ξ Φ Γ C A)))
      (g : Tm Ξ Φ Γ (Pi Ξ Φ Γ B (weakenTy Ξ Φ Γ C B)))
      (a : Tm Ξ Φ Γ A) where
    conclusion : eqTerm Ξ Φ Γ C (coprodElim Ξ Φ Γ A B C f g (inl Ξ Φ Γ A B a))
      (convTm Ξ Φ Γ (substTy Ξ Φ Γ A (weakenTy Ξ Φ Γ C A) a) C
        (app Ξ Φ Γ A (weakenTy Ξ Φ Γ C A) f a))
  rule coprod_beta_inr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ Γ) (C : Ty Ξ Φ Γ)
      (f : Tm Ξ Φ Γ (Pi Ξ Φ Γ A (weakenTy Ξ Φ Γ C A)))
      (g : Tm Ξ Φ Γ (Pi Ξ Φ Γ B (weakenTy Ξ Φ Γ C B)))
      (b : Tm Ξ Φ Γ B) where
    conclusion : eqTerm Ξ Φ Γ C (coprodElim Ξ Φ Γ A B C f g (inr Ξ Φ Γ A B b))
      (convTm Ξ Φ Γ (substTy Ξ Φ Γ B (weakenTy Ξ Φ Γ C B) b) C
        (app Ξ Φ Γ B (weakenTy Ξ Φ Γ C B) g b))

  /-
  Identity-type gap: `idTransport` is a transport primitive rather than a full dependent identity
  eliminator.  A complete specification should state the eliminator, β rule, congruence, and the
  derived path algebra needed for equivalences and Rezk completeness.
  -/
  lf_opaque Id (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A) : Ty Ξ Φ Γ
  lf_opaque reflTm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) : Tm Ξ Φ Γ (Id Ξ Φ Γ A a a)
  lf_opaque idTransport (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
    (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A)
    (p : Tm Ξ Φ Γ (Id Ξ Φ Γ A a b))
    (u : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)) : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B b)
  rule id_elim_beta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (B : Ty Ξ Φ (extendTyCtx Ξ Φ Γ A))
      (a : Tm Ξ Φ Γ A) (u : Tm Ξ Φ Γ (substTy Ξ Φ Γ A B a)) where
    conclusion : eqTerm Ξ Φ Γ (substTy Ξ Φ Γ A B a)
      (idTransport Ξ Φ Γ A B a a (reflTm Ξ Φ Γ A a) u) u
  rule id_congr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (b : Tm Ξ Φ Γ A)
      (a' : Tm Ξ Φ Γ A) (b' : Tm Ξ Φ Γ A) where
    premise left_eq : eqTerm Ξ Φ Γ A a a'
    premise right_eq : eqTerm Ξ Φ Γ A b b'
    conclusion : eqType Ξ Φ Γ (Id Ξ Φ Γ A a b) (Id Ξ Φ Γ A a' b')

  /-
  Contractibility gap: `IsContr` is primitive.  For a full object theory it should be the standard
  dependent-pair package containing a center and paths from the center to each point.  That change
  also supplies the projections below by checked definitions.
  -/
  lf_opaque IsContr (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) : Ty Ξ Φ Γ
  lf_opaque isContrCenter (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (c : Tm Ξ Φ Γ (IsContr Ξ Φ Γ A)) : Tm Ξ Φ Γ A
  lf_opaque isContrPath (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (c : Tm Ξ Φ Γ (IsContr Ξ Φ Γ A))
    (x : Tm Ξ Φ Γ A) : Tm Ξ Φ Γ (Id Ξ Φ Γ A (isContrCenter Ξ Φ Γ A c) x)

  /-- Tope equality, cube weakening/substitution, and tope restriction. -/
  /-
  Missing reindexing and restriction laws:

  This region is the main structural bottleneck.  A complete SHoTT specification should present
  reindexing along arbitrary cube substitutions, restriction to tope assumptions, and substitution
  of cube points as functorial operations on contexts, types, terms, and evidence.  Required laws
  include identities, composition, interaction with ordinary substitution, interaction with tope
  logical connectives, and preservation of every type former above.

  Equality topes also need a replacement principle.  `substTyTopeEq` and `substTmTopeEq` name part
  of that principle, but the full theory needs replacement through topes, shape presentations,
  extension boundaries, and evidence terms.
  -/
  lf_opaque substTyTopeEq (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube) (i : CubeTm Ξ I) (j : CubeTm Ξ I) (A : Ty Ξ Φ Γ) : Ty Ξ Φ Γ
  lf_opaque substTmTopeEq (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube) (i : CubeTm Ξ I) (j : CubeTm Ξ I) (A : Ty Ξ Φ Γ)
    (a : Tm Ξ Φ Γ A) : Tm Ξ Φ Γ (substTyTopeEq Ξ Φ Γ I i j A)
  rule eqType_tope_eq_subst (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (I : Cube) (i : CubeTm Ξ I) (j : CubeTm Ξ I) (A : Ty Ξ Φ Γ) where
    premise path : entails Ξ Φ (topeEq Ξ I i j)
    conclusion : eqType Ξ Φ Γ A (substTyTopeEq Ξ Φ Γ I i j A)

  lf_opaque weakenTopeCtxCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (I : Cube) :
    TopeCtx (extendCubeCtx Ξ I)
  lf_opaque weakenTyCtxCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube) : TyCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
  lf_opaque weakenTyCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (I : Cube) :
      Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) (weakenTyCtxCube Ξ Φ Γ I)
  lf_opaque weakenTmCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (I : Cube) :
      Tm (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) (weakenTyCube Ξ Φ Γ A I)
  lf_opaque restrictTyCtxTope (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (φ : Tope Ξ) : TyCtx Ξ (extendTopeCtx Ξ Φ φ)
  lf_opaque restrictTyTope (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (φ : Tope Ξ) :
      Ty Ξ (extendTopeCtx Ξ Φ φ) (restrictTyCtxTope Ξ Φ Γ φ)
  lf_opaque restrictTmTope (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (A : Ty Ξ Φ Γ) (a : Tm Ξ Φ Γ A) (φ : Tope Ξ) :
      Tm Ξ (extendTopeCtx Ξ Φ φ) (restrictTyCtxTope Ξ Φ Γ φ)
        (restrictTyTope Ξ Φ Γ A φ)

  lf_opaque substTopeCube (Ξ : CubeCtx) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (s : CubeTm Ξ I) : Tope Ξ
  lf_opaque substTyCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube)
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (s : CubeTm Ξ I) : Ty Ξ Φ Γ
  /-
  Specification hole: substituting a term defined under the tope `φ` at a point `s` should require
  evidence for `φ[s]`, or it should return a term in a context extended by `φ[s]`.  The declaration
  below is permissive because it lacks that membership evidence.
  -/
  lf_opaque substTmCube (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube) (φ : Tope (extendCubeCtx Ξ I))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (s : CubeTm Ξ I) : Tm Ξ Φ Γ (substTyCube Ξ Φ Γ I A s)
  rule subst_ty_cube_weaken (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (A : Ty Ξ Φ Γ) (I : Cube) (s : CubeTm Ξ I) where
    conclusion : eqType Ξ Φ Γ (substTyCube Ξ Φ Γ I (weakenTyCube Ξ Φ Γ A I) s) A

  /-- Disjunctive gluing for topes. -/
  /-
  Missing disjunctive computation rules:

  `branchTm` should compute to the left branch under `φ`, to the right branch under `ψ`, and satisfy
  a uniqueness/η rule over `φ ∨ ψ`.  The overlap data should be tied to actual restrictions of the
  branches to `φ ∧ ψ`, rather than arbitrary terms supplied by the caller.  The theory also needs a
  bottom-elimination term former for ordinary terms in an impossible tope context.
  -/
  lf_opaque branchTm (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (φ : Tope Ξ) (ψ : Tope Ξ) (A : Ty Ξ Φ Γ)
    (left : Tm Ξ (extendTopeCtx Ξ Φ φ) (restrictTyCtxTope Ξ Φ Γ φ)
      (restrictTyTope Ξ Φ Γ A φ))
    (right : Tm Ξ (extendTopeCtx Ξ Φ ψ) (restrictTyCtxTope Ξ Φ Γ ψ)
      (restrictTyTope Ξ Φ Γ A ψ))
    (leftOverlap : Tm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
      (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
      (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)))
    (rightOverlap : Tm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
      (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
      (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)))
    (overlap : EqTermEvidence Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
      (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
      (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)) leftOverlap rightOverlap) :
      Tm Ξ (extendTopeCtx Ξ Φ (topeOr Ξ φ ψ))
        (restrictTyCtxTope Ξ Φ Γ (topeOr Ξ φ ψ))
        (restrictTyTope Ξ Φ Γ A (topeOr Ξ φ ψ))
  rule branch_tm_overlap (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
      (φ : Tope Ξ) (ψ : Tope Ξ) (A : Ty Ξ Φ Γ)
      (left : Tm Ξ (extendTopeCtx Ξ Φ φ) (restrictTyCtxTope Ξ Φ Γ φ)
        (restrictTyTope Ξ Φ Γ A φ))
      (right : Tm Ξ (extendTopeCtx Ξ Φ ψ) (restrictTyCtxTope Ξ Φ Γ ψ)
        (restrictTyTope Ξ Φ Γ A ψ))
      (leftOverlap : Tm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
        (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
        (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)))
      (rightOverlap : Tm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
        (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
        (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ))) where
    premise overlap : eqTerm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
      (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
      (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)) leftOverlap rightOverlap
    conclusion : eqTerm Ξ (extendTopeCtx Ξ Φ (topeAnd Ξ φ ψ))
      (restrictTyCtxTope Ξ Φ Γ (topeAnd Ξ φ ψ))
      (restrictTyTope Ξ Φ Γ A (topeAnd Ξ φ ψ)) leftOverlap rightOverlap

  /-- Dependent extension types over a shape inclusion.

  The inclusion is first-class evidence, so an extension type can only be formed from a declared
  subshape `{t : I | φ} ⊆ {t : I | ψ}`.

  Missing extension-type specification:

  * The larger-shape section `b` in `extIntro` should restrict to the smaller shape by a canonical
    restriction operation induced by `incl`; the present `bBoundary` argument is a temporary way to
    name that restriction.
  * Point application should have β rules for introduced sections and boundary rules at points
    satisfying the smaller-shape tope `φ`.
  * Extension types should be stable under cube substitution, tope restriction, ordinary
    substitution, and conversion, with stated coherence laws.
  * Section 4 of the paper requires extension-type equivalences: currying/interchange of extension
    variables, interaction with `Π`, `Σ`, identity, coproduct/disjunction, and relative function
    extensionality.  Only a single `relExtFunext` primitive appears below.
  -/
  lf_opaque Ext (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ)) : Ty Ξ Φ Γ

  /-- Introduction for extension types from a section over the larger shape and first-class
  evidence that its boundary restriction agrees with the prescribed partial section.
  -/
  lf_opaque extIntro (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (b : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) ψ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) ψ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A ψ))
    (bBoundary : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (boundary : EqTermEvidence (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ) bBoundary a) :
      Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)

  /-- Elimination exposes the section over the larger shape. -/
  lf_opaque extApp (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) :
      Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) ψ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) ψ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A ψ)

  /-- Boundary projection of an extension term. -/
  lf_opaque extAppBoundary (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) :
      Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ)

  /-- Point application for an extension term at a point satisfying the larger-shape tope. -/
  lf_opaque extAppPoint (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (s : CubeTm Ξ I) (point_ok : EntailsEvidence Ξ Φ (substTopeCube Ξ I ψ s))
    (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) :
      Tm Ξ Φ Γ (substTyCube Ξ Φ Γ I A s)

  /-- First-class evidence that every extension term restricts to the prescribed partial
  section on the smaller shape.
  -/
  lf_opaque extBoundaryEvidence (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ)
    (I : Cube) (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) :
    EqTermEvidence (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ)
      (extAppBoundary Ξ Φ Γ I φ ψ incl A a f) a

  rule ext_boundary (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
      (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
      (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
      (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I))
      (a : Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ))
      (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) where
    conclusion : eqTerm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ)
      (extAppBoundary Ξ Φ Γ I φ ψ incl A a f) a

  rule ext_beta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
      (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
      (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
      (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I))
      (a : Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ))
      (b : Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) ψ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) ψ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A ψ))
      (bBoundary : Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ))
      (boundary : EqTermEvidence (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ) bBoundary a) where
    conclusion : eqTerm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) ψ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) ψ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A ψ)
      (extApp Ξ Φ Γ I φ ψ incl A a (extIntro Ξ Φ Γ I φ ψ incl A a b bBoundary boundary)) b

  rule ext_eta (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
      (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
      (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
      (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I))
      (a : Tm (extendCubeCtx Ξ I)
        (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
        (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) φ)
        (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A φ))
      (f : Tm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a)) where
    conclusion : eqTerm Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a) f
      (extIntro Ξ Φ Γ I φ ψ incl A a (extApp Ξ Φ Γ I φ ψ incl A a f)
        (extAppBoundary Ξ Φ Γ I φ ψ incl A a f)
        (extBoundaryEvidence Ξ Φ Γ I φ ψ incl A a f))

  /-
  Relative extension function extensionality gap:

  The paper proves a family of equivalences showing that extension types preserve contractibility
  and commute with type formers.  This primitive records the most visible consequence, but a full
  specification should state the surrounding equivalences and their computation behavior, then make
  this term a derived construction where possible.
  -/
  lf_opaque relExtFunext (Ξ : CubeCtx) (Φ : TopeCtx Ξ) (Γ : TyCtx Ξ Φ) (I : Cube)
    (φ : Tope (extendCubeCtx Ξ I)) (ψ : Tope (extendCubeCtx Ξ I))
    (incl : ShapeInclEvidence (shapeOf Ξ I φ) (shapeOf Ξ I ψ))
    (A : Ty (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
      (weakenTyCtxCube Ξ Φ Γ I))
    (a : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) φ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) φ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) A φ))
    (c : Tm (extendCubeCtx Ξ I)
      (extendTopeCtx (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I) ψ)
      (restrictTyCtxTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I) ψ)
      (restrictTyTope (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
        (weakenTyCtxCube Ξ Φ Γ I)
        (IsContr (extendCubeCtx Ξ I) (weakenTopeCtxCube Ξ Φ I)
          (weakenTyCtxCube Ξ Φ Γ I) A) ψ)) :
      Tm Ξ Φ Γ (IsContr Ξ Φ Γ (Ext Ξ Φ Γ I φ ψ incl A a))

namespace SHoTT

/-
Low-dimensional shape library gaps:

The definitions below provide only the shapes needed to name the first hom/Segal/Rezk placeholders.
A full syntactic specification should include a reusable family of simplices `Δⁿ`, boundaries
`∂Δⁿ`, horns `Λⁿₖ`, face and degeneracy maps, inclusions between these shapes, and laws relating
those maps to the tope presentations.  The checked definitions should avoid one-off geometry for
only `n = 1` and `n = 2`.
-/

/-- Cube context with one interval coordinate. -/
internal def intervalCtx : CubeCtx := extendCubeCtx emptyCubeCtx interval

/-- The distinguished interval coordinate in the one-interval cube context. -/
internal def intervalVar : CubeTm (extendCubeCtx emptyCubeCtx interval) interval :=
  cubeVarTerm (extendCubeCtx emptyCubeCtx interval) interval (lastCubeVar emptyCubeCtx interval)

/-- Tope cutting out the boundary of the interval. -/
internal def boundary1Tope : Tope (extendCubeCtx emptyCubeCtx interval) :=
  topeOr (extendCubeCtx emptyCubeCtx interval)
    (topeEq (extendCubeCtx emptyCubeCtx interval) interval intervalVar
      (zero (extendCubeCtx emptyCubeCtx interval)))
    (topeEq (extendCubeCtx emptyCubeCtx interval) interval intervalVar
      (one (extendCubeCtx emptyCubeCtx interval)))

/-- Standard-library 1-simplex shape, represented as the full interval. -/
internal def simplex1 : Shape emptyCubeCtx :=
  shapeOf emptyCubeCtx interval (top (extendCubeCtx emptyCubeCtx interval))

/-- Standard-library boundary of the 1-simplex. -/
internal def boundary1 : Shape emptyCubeCtx :=
  shapeOf emptyCubeCtx interval boundary1Tope

/-- Cube context with one product-of-intervals coordinate. -/
internal def simplex2Ctx : CubeCtx := extendCubeCtx emptyCubeCtx (prod interval interval)

/-- The paired coordinates of the 2-simplex presentation. -/
internal def simplex2Var :
    CubeTm (extendCubeCtx emptyCubeCtx (prod interval interval)) (prod interval interval) :=
  cubeVarTerm (extendCubeCtx emptyCubeCtx (prod interval interval)) (prod interval interval)
    (lastCubeVar emptyCubeCtx (prod interval interval))

/-- First coordinate of the 2-simplex presentation. -/
internal def simplex2Left :
    CubeTm (extendCubeCtx emptyCubeCtx (prod interval interval)) interval :=
  pi1 (extendCubeCtx emptyCubeCtx (prod interval interval)) interval interval simplex2Var

/-- Second coordinate of the 2-simplex presentation. -/
internal def simplex2Right :
    CubeTm (extendCubeCtx emptyCubeCtx (prod interval interval)) interval :=
  pi2 (extendCubeCtx emptyCubeCtx (prod interval interval)) interval interval simplex2Var

/-- Tope presentation of the 2-simplex as ordered interval coordinates.  Paper
convention: `Δ² = {⟨t₁, t₂⟩ : 2 × 2 | t₂ ≤ t₁}`.
-/
internal def simplex2Tope : Tope (extendCubeCtx emptyCubeCtx (prod interval interval)) :=
  leq (extendCubeCtx emptyCubeCtx (prod interval interval)) simplex2Right simplex2Left

/-- Tope presentation of the boundary of the 2-simplex.  With the paper coordinate convention,
the three faces are `t₂ = 0`, `t₂ = t₁`, and `t₁ = 1`.
-/
internal def boundary2Tope : Tope (extendCubeCtx emptyCubeCtx (prod interval interval)) :=
  topeOr (extendCubeCtx emptyCubeCtx (prod interval interval))
    (topeOr (extendCubeCtx emptyCubeCtx (prod interval interval))
      (topeEq (extendCubeCtx emptyCubeCtx (prod interval interval)) interval simplex2Right
        (zero (extendCubeCtx emptyCubeCtx (prod interval interval))))
      (topeEq (extendCubeCtx emptyCubeCtx (prod interval interval)) interval simplex2Left
        (one (extendCubeCtx emptyCubeCtx (prod interval interval)))))
    (topeEq (extendCubeCtx emptyCubeCtx (prod interval interval)) interval simplex2Right
      simplex2Left)

/-- Tope presentation of the `(2,1)`-horn, omitting the diagonal face. -/
internal def horn21Tope : Tope (extendCubeCtx emptyCubeCtx (prod interval interval)) :=
  topeOr (extendCubeCtx emptyCubeCtx (prod interval interval))
    (topeEq (extendCubeCtx emptyCubeCtx (prod interval interval)) interval simplex2Right
      (zero (extendCubeCtx emptyCubeCtx (prod interval interval))))
    (topeEq (extendCubeCtx emptyCubeCtx (prod interval interval)) interval simplex2Left
      (one (extendCubeCtx emptyCubeCtx (prod interval interval))))

/-- Standard-library 2-simplex shape. -/
internal def simplex2 : Shape emptyCubeCtx :=
  shapeOf emptyCubeCtx (prod interval interval) simplex2Tope

/-- Standard-library boundary of the 2-simplex. -/
internal def boundary2 : Shape emptyCubeCtx :=
  shapeOf emptyCubeCtx (prod interval interval) boundary2Tope

/-- Standard-library `(2,1)`-horn shape. -/
internal def horn21 : Shape emptyCubeCtx :=
  shapeOf emptyCubeCtx (prod interval interval) horn21Tope

/-- Checked standard-library alias for the 1-simplex shape. -/
internal def Delta1 : Shape emptyCubeCtx := simplex1

/-- Checked standard-library alias for the boundary of the 1-simplex. -/
internal def BoundaryDelta1 : Shape emptyCubeCtx := boundary1

/-- Checked standard-library alias for the 2-simplex shape. -/
internal def Delta2 : Shape emptyCubeCtx := simplex2

/-- Checked standard-library alias for the boundary of the 2-simplex. -/
internal def BoundaryDelta2 : Shape emptyCubeCtx := boundary2

/-- Checked standard-library alias for the `(2,1)`-horn shape. -/
internal def Horn21 : Shape emptyCubeCtx := horn21

/-
The next three inclusions should be checked evidence constructed from the tope calculus.  They are
currently admitted because the entailment/evidence layer lacks enough reusable constructors and
substitution laws to derive the inclusions from the displayed formulas.
-/

/-- The boundary of Δ¹ is included in Δ¹, as first-class extension-side-condition evidence. -/
internal def boundary1_in_delta1 : ShapeInclEvidence BoundaryDelta1 Delta1 := sorry

/-- The `(2,1)`-horn is included in Δ², as first-class extension-side-condition evidence. -/
internal def horn21_in_delta2 : ShapeInclEvidence Horn21 Delta2 := sorry

/-- The boundary of Δ² is included in Δ², as first-class extension-side-condition evidence. -/
internal def boundary2_in_delta2 : ShapeInclEvidence BoundaryDelta2 Delta2 := sorry

/-
Hom/Segal/Rezk specification gaps:

These shape constructors are placeholders for a much larger object-theory layer.  The full theory
should define hom types from extension types over `Δ¹` with prescribed endpoint boundary data,
define composition and associativity from fillers over `Δ²`, express the Segal condition as
contractibility or equivalence of composite data, and state Rezk completeness using the internal
`idtoiso`/equivalence package.  These should be ordinary type-theoretic definitions and judgments,
not just names for shapes.

The future layer should also include covariant families, the Yoneda lemma, and adjunctions as
object-theory constructions once the hom and Segal infrastructure exists.  Those topics still
belong to the specification, even though model semantics is outside this file's immediate scope.
-/

/-- Admitted hom-shape constructor. -/
internal def homShape : (S : Shape emptyCubeCtx) → Shape emptyCubeCtx := sorry

/-- Admitted hom2-shape constructor. -/
internal def hom2Shape : (S : Shape emptyCubeCtx) → Shape emptyCubeCtx := sorry

/-- Admitted Segal-shape constructor. -/
internal def SegalShape : (S : Shape emptyCubeCtx) → Shape emptyCubeCtx := sorry

/-- Admitted Rezk-shape constructor. -/
internal def RezkShape : (S : Shape emptyCubeCtx) → Shape emptyCubeCtx := sorry

internal def hom : Shape emptyCubeCtx := homShape Delta1
internal def hom2 : Shape emptyCubeCtx := hom2Shape Delta2
internal def Segal : Shape emptyCubeCtx := SegalShape Delta2
internal def Rezk : Shape emptyCubeCtx := RezkShape Delta2

end SHoTT
