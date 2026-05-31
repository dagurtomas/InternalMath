/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter2.Cores

@[expose] public section

/-- Chapter 3: subcategories, localizations, realizations, joins, and slices; Axioms H--J.2. -/
extend_type_theory SCT where

  model_section Chapter3


  /-- Product context used to describe Construction 3.1.1: a functor `X → C` together with an
  arrow of `X`. -/
  lf_def arrowActionContext : (X : SCat) ⇒ (C : SCat) ⇒ SCat :=
    fun X C => prodCat (funCat X C) (funCat intervalCat X)
  /-- Total context for evaluating a functor `X → C` on an arrow of `X`. -/
  lf_def arrowActionTotalContext : (X : SCat) ⇒ (C : SCat) ⇒ SCat :=
    fun X C => prodCat (arrowActionContext X C) intervalCat
  /-- Projection to the functor parameter in Construction 3.1.1. -/
  lf_def arrowActionParameterFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) (funCat X C) :=
    fun X C => compFunctor (arrowActionTotalContext X C) (arrowActionContext X C)
      (funCat X C) (prodPr1 (arrowActionContext X C) intervalCat)
      (prodPr1 (funCat X C) (funCat intervalCat X))
  /-- Projection to the arrow parameter in Construction 3.1.1. -/
  lf_def arrowActionArgumentFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) (funCat intervalCat X) :=
    fun X C => compFunctor (arrowActionTotalContext X C) (arrowActionContext X C)
      (funCat intervalCat X) (prodPr1 (arrowActionContext X C) intervalCat)
      (prodPr2 (funCat X C) (funCat intervalCat X))
  /-- Projection to the interval parameter in Construction 3.1.1. -/
  lf_def arrowActionIntervalFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) intervalCat :=
    fun X C => prodPr2 (arrowActionContext X C) intervalCat
  /-- Evaluation of the selected arrow of `X` at the interval parameter. -/
  lf_def arrowActionInputObject : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) X :=
    fun X C => compFunctor (arrowActionTotalContext X C)
      (prodCat (funCat intervalCat X) intervalCat) X
      (prodPair (arrowActionTotalContext X C) (funCat intervalCat X) intervalCat
        (arrowActionArgumentFunctor X C) (arrowActionIntervalFunctor X C))
      (evalFunctor intervalCat X)
  /-- Pair consisting of the selected functor `X → C` and the selected object of `X`. -/
  lf_def arrowActionEvalPair : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) (prodCat (funCat X C) X) :=
    fun X C => prodPair (arrowActionTotalContext X C) (funCat X C) X
      (arrowActionParameterFunctor X C) (arrowActionInputObject X C)
  /-- Evaluation of a functor `X → C` on an arrow of `X`, before currying. -/
  lf_def arrowActionEvalFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionTotalContext X C) C :=
    fun X C => compFunctor (arrowActionTotalContext X C) (prodCat (funCat X C) X) C
      (arrowActionEvalPair X C) (evalFunctor X C)
  /-- Construction 3.1.1 before the final currying step. -/
  lf_def arrowActionObjectFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (arrowActionContext X C) (funCat intervalCat C) :=
    fun X C => curryFunctor (arrowActionContext X C) intervalCat C
      (arrowActionEvalFunctor X C)
  /-- Construction 3.1.1: a functor induces a functor on arrow categories by postcomposition. -/
  lf_def arrowActionFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (funCat X C) (funCat (funCat intervalCat X) (funCat intervalCat C)) :=
    fun X C => curryFunctor (funCat X C) (funCat intervalCat X) (funCat intervalCat C)
      (arrowActionObjectFunctor X C)
  /-- Mapping anima represented as the core of the functor category. -/
  lf_def mapCat : (X : SCat) ⇒ (C : SCat) ⇒ SCat :=
    fun X C => coreCat (funCat X C)
  /-- Postcomposition on mapping anima, represented through functor-category cores. -/
  lf_def mapPostcompFunctor : (X : SCat) ⇒ (A : SCat) ⇒ (C : SCat) ⇒ Functor A C ⇒
      Functor (mapCat X A) (mapCat X C) :=
    fun X A C i => coreFunctor (funCat X A) (funCat X C) (postcompFunctor X A C i)
  /-- Construction 3.1.1 on mapping anima, represented through functor-category cores. -/
  lf_def arrowActionMapFunctor : (X : SCat) ⇒ (C : SCat) ⇒
      Functor (mapCat X C) (mapCat (funCat intervalCat X) (funCat intervalCat C)) :=
    fun X C => coreFunctor (funCat X C)
      (funCat (funCat intervalCat X) (funCat intervalCat C)) (arrowActionFunctor X C)
  /-- Definition 3.1.2(1): the induced map on arrow-mapping anima is an embedding. -/
  syntax_abbrev SubcategoryArrowEmbedding (A : SCat) (C : SCat) (i : Functor A C) :=
    Embedding (mapCat intervalCat A) (mapCat intervalCat C)
      (mapPostcompFunctor intervalCat A C i)
  /-- Definition 3.1.2(2): the factorization square for a fixed test category. -/
  syntax_abbrev SubcategoryPullbackSquare (A : SCat) (C : SCat) (i : Functor A C)
    (X : SCat) :=
    PullbackSquare (mapCat X A) (mapCat X C)
      (mapCat (funCat intervalCat X) (funCat intervalCat A))
      (mapCat (funCat intervalCat X) (funCat intervalCat C))
      (mapPostcompFunctor X A C i) (arrowActionMapFunctor X A)
      (arrowActionMapFunctor X C)
      (mapPostcompFunctor (funCat intervalCat X) (funCat intervalCat A)
        (funCat intervalCat C) (postcompFunctor intervalCat A C i))
  /-- Definition 3.1.2(2), uniformly in the test category. -/
  syntax_abbrev SubcategoryPullbackCriterion (A : SCat) (C : SCat) (i : Functor A C) :=
    (X : SCat) → SubcategoryPullbackSquare A C i X
  /-- A functor satisfying the book's replete subcategory criterion; Definition 3.1.2. -/
  syntax_abbrev SubcategoryWitness (A : SCat) (C : SCat) (i : Functor A C) :=
    Σ arrow_emb : SubcategoryArrowEmbedding A C i, SubcategoryPullbackCriterion A C i
  /-- Projection of the arrow-map embedding part of a subcategory witness. -/
  lf_def subcategoryWitnessArrowEmbedding : (A : SCat) ⇒ (C : SCat) ⇒
      (i : Functor A C) ⇒ SubcategoryWitness A C i ⇒ SubcategoryArrowEmbedding A C i :=
    fun A C i h => fst h

  /-- Subobjects of an anima, represented by a domain anima, an inclusion, and embedding evidence;
  Definition 3.1.6. -/
  syntax_abbrev AnimaSubobject (A : Anima) :=
    Σ B : Anima, Σ i : Functor (animaCat B) (animaCat A),
      Embedding (animaCat B) (animaCat A) i

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- The identity functor is a subcategory; Example 3.1.4.
  Status: temporary sorry-admitted structural theorem package; not a model field. -/
  def idSubcategoryWitness (C : SCat) : SubcategoryWitness C C (idFunctor C) := sorry
  /-- The initial inclusion is a subcategory; Example 3.1.4.
  Status: temporary sorry-admitted structural theorem package; not a model field. -/
  def initialSubcategoryWitness (C : SCat) :
      SubcategoryWitness initialCat C (initialElim C) := sorry
  /-- Every subcategory is an embedding.
  Book target: Lemma 3.1.5.
  Status: temporary theorem-shaped sorry-admitted internal declaration; not a model field. -/
  def subcategoryWitnessEmbedding (A : SCat) (C : SCat) (i : Functor A C)
    (h : SubcategoryWitness A C i) : Embedding A C i := sorry

end SCT
