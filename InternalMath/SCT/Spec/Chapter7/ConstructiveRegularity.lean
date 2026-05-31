/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter7.StraighteningUnstraightening

@[expose] public section

namespace SCT

internal_defs where
  /-- Universal composable pair of small cocartesian fibrations.
  Book target: §7.8.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def universalComposablePairCat (U : SCat) (u : UniverseWitness U) : SCat := sorry

  /-- Projection from the universal composable-pair category.
  Book target: §7.8.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def universalComposablePairProjection (U : SCat) (u : UniverseWitness U) :
    Functor (universalComposablePairCat U u) U := sorry

end SCT

extend_type_theory SCT where

  model_section Chapter7

  /-- The fixed universe classifies cocartesian fibrations; Axiom N. -/
  lf_opaque directed_univalence_classifies (E : SCat) (B : SCat) (p : Functor E B)
    (fib : Fibration E B p) (cocart : CocartesianFibrationWitness E B p fib) :
    SmallCocartesianFibrationWitness categoryUniverse E B p fib cocart

namespace SCT

internal_defs where
  /-- Constructive regularity implies regularity.
  Book target: §7.8.
  Status: temporary sorry-admitted internal declaration; not a model-provider field. -/
  def regularOfConstructiveRegular (U : SCat) (u : UniverseWitness U)
    (h : ConstructiveRegularUniverseWitness U u) : RegularUniverseWitness U u := sorry

end SCT
