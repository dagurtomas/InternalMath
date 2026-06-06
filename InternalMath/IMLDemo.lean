import InternalLean

declare_type_theory MyTypeTheory where
  /-- Internal types -/
  syntax_sort Ty : Type 1
  /-- Internal terms -/
  syntax_sort Tm (A : Ty)
  /-- An internal type (`lf_opaque` means primitive/axiom) -/
  lf_opaque type : Ty
  /-- A term of the given type `type` -/
  lf_opaque term : Tm type

namespace MyTypeTheory

/--  -/
internal def myType : Ty := type

internal def myTerm : Tm myType := term

end MyTypeTheory

open MyTypeTheory

section Model1

generate_model_interface MyTypeTheory as MyModel

#check MyModel

def model : MyModel where
  Ty := Type
  Tm ty := ty
  type := Unit
  term := ()

#check model.Ty
#check model.Tm

generate_model_transports MyTypeTheory for MyModel

end Model1

section Model2

#check model.myType
#check model.myTerm

def tm : Unit := model.myTerm

theorem myTerm_eq_unit : model.myTerm = () := by
  dsimp [model]

def otherModel : MyModel where
  Ty := Type
  Tm ty := ty
  type := Nat
  term := 0

theorem myTerm_eq_zero : otherModel.myTerm = (0 : Nat) := by
  dsimp [otherModel, MyModel.myTerm]

end Model2
