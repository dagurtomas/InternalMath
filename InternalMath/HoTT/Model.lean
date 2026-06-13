/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.HoTT.HoTT

/-!
# Generated HoTT model interface

This file materializes the generated InternalLean model interface for the Appendix A.3 HoTT
specification and records a field-by-field placeholder model.  Each field of `sorryModel` is a
`sorry`, so the declaration is only an obligation skeleton for inspecting the semantic contract.
-/

@[expose] public section

generate_model_interface HoTT as HoTTModel

namespace HoTT

/-- A placeholder model of the generated HoTT interface, with every field left as `sorry`. -/
def sorryModel : HoTTModel where
  Ctx := sorry
  Ty := sorry
  Tm := sorry
  Sub := sorry
  UnivLevel := sorry
  emptyCtx := sorry
  extendCtx := sorry
  idSub := sorry
  compSub := sorry
  weakenSub := sorry
  substTy := sorry
  substTm := sorry
  extendSub := sorry
  varTop := sorry
  piTy := sorry
  lam := sorry
  app := sorry
  sigmaTy := sorry
  sigmaPair := sorry
  sigmaInd := sorry
  coprodTy := sorry
  coprodInl := sorry
  coprodInr := sorry
  coprodInd := sorry
  emptyTy := sorry
  emptyInd := sorry
  unitTy := sorry
  unitStar := sorry
  unitInd := sorry
  natTy := sorry
  natZero := sorry
  natSucc := sorry
  natInd := sorry
  idTy := sorry
  refl := sorry
  idInd := sorry
  levelZero := sorry
  levelSucc := sorry
  univ := sorry
  elTy := sorry
  funext := sorry
  univalence := sorry
  circleTy := sorry
  circleBase := sorry
  circleLoop := sorry
  circleInd := sorry
  circleLoopComp := sorry
  IsCtx := sorry
  IsTy := sorry
  IsTm := sorry
  EqTm := sorry
  ctx_EMP := sorry
  ctx_EXT := sorry
  substTy_form := sorry
  wkgTy_form := sorry
  vble := sorry
  subst_1 := sorry
  wkg_1 := sorry
  subst_2 := sorry
  subst_3 := sorry
  wkg_2 := sorry
  eq_refl := sorry
  eq_symm := sorry
  eq_trans := sorry
  pi_form := sorry
  pi_intro := sorry
  pi_elim := sorry
  pi_comp := sorry
  pi_uniq := sorry
  pi_intro_eq := sorry
  sigma_form := sorry
  sigma_intro := sorry
  sigma_elim := sorry
  sigma_comp := sorry
  coprod_form := sorry
  coprod_intro_left := sorry
  coprod_intro_right := sorry
  coprod_elim := sorry
  coprod_comp_left := sorry
  coprod_comp_right := sorry
  empty_form := sorry
  empty_elim := sorry
  unit_form := sorry
  unit_intro := sorry
  unit_elim := sorry
  unit_comp := sorry
  nat_form := sorry
  nat_intro_zero := sorry
  nat_intro_succ := sorry
  nat_elim := sorry
  nat_comp_zero := sorry
  nat_comp_succ := sorry
  id_form := sorry
  id_intro := sorry
  id_elim := sorry
  id_comp := sorry
  univ_form := sorry
  el_form := sorry
  pi_ext := sorry
  univ_univ := sorry
  circle_form := sorry
  circle_intro_base := sorry
  circle_intro_loop := sorry
  circle_elim := sorry
  circle_comp_base := sorry
  circle_comp_loop := sorry

end HoTT
