/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec.Chapter6.StrongSurjectivity

@[expose] public section

namespace SCT

/- Theorem-shaped declarations are admitted temporarily while moved out of the model interface. -/
internal_defs where
  /-- A retraction makes a functor conservative.
  Book target: §6.2, retract arguments for conservativity.
  Status: temporary sorry-admitted internal declaration; not a model-provider field.
  To finish this declaration: prove by composing the retraction data with the conservative
  criterion. -/
  def conservativeOfRetract (C : SCat) (D : SCat) (F : Functor C D)
    (R : Functor D C) (ρ : NatIso C C (compFunctor C D C F R) (idFunctor C)) :
    Conservative C D F := sorry

end SCT
