module

public import InternalMath.LambdaCalculus.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Models and Curry--Howard--Lambek comparison for STLC

This file connects the InternalLean simply typed lambda calculus from `Basic.lean` with ordinary
`mathlib` category theory.

There are three main constructions:

* `CCC.lambdaCalculusModel` interprets STLC in any cartesian closed category.
* For an arbitrary `LambdaCalculusModel`, the types and one-variable terms modulo definitional
  equality form a syntactic cartesian closed category.
* For a cartesian closed category `C`, the canonical functor from `C` to the syntactic category of
  its interpreted STLC model is an equivalence.  The final section records the quotient-level
  comparison between arbitrary contexts and morphisms out of their representing objects.

The generated model interface is used as a semantic contract.  The later declarations are ordinary
Lean definitions and instances built from that contract.
-/

@[expose] public section

generate_model_interface LambdaCalculus as LambdaCalculusModel
generate_model_transports LambdaCalculus only weakenTm substTop homComp for LambdaCalculusModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory LambdaCalculus

section CurryHowardLambekForward

variable (C : Type) [Category C] [CartesianMonoidalCategory C] [MonoidalClosed C]

def CCC.lambdaCalculusModel : LambdaCalculusModel where
  Ctx := C
  Ty := C
  Tm X Y := X ⟶ Y
  Sub X Y := X ⟶ Y
  unitTy := 𝟙_ C
  prodTy X Y := X ⊗ Y
  arrowTy X Y := X ⟶[C] Y
  emptyCtx := 𝟙_ C
  extendCtx X Y := X ⊗ Y
  idSub X := 𝟙 X
  compSub _ _ _ σ τ := σ ≫ τ
  emptySub Γ := toUnit Γ
  weakenSub Γ A := «fst» Γ A
  extendSub _ _ _ σ t := lift σ t
  substTm _ _ _ σ t := σ ≫ t
  varZero Γ A := «snd» Γ A
  ctxObj Γ := Γ
  ctxToSingleton Γ := lift (toUnit Γ) (𝟙 Γ)
  ctxFromSingleton Γ := «snd» (𝟙_ C) Γ
  unitIntro Γ := toUnit Γ
  pairTm _ _ _ fstArg sndArg := lift fstArg sndArg
  fstTm _ A B pair := pair ≫ «fst» A B
  sndTm _ A B pair := pair ≫ «snd» A B
  lam Γ A _ body := MonoidalClosed.curry (lift («snd» A Γ) («fst» A Γ) ≫ body)
  app _ A B fn arg := lift arg fn ≫ (ihom.ev A).app B
  EqTm _ _ t u := PLift (t = u)
  EqSub _ _ σ τ := PLift (σ = τ)
  eq_refl _ _ _ := ⟨rfl⟩
  eq_symm _ _ _ _ h := ⟨h.down.symm⟩
  eq_trans _ _ _ _ _ h₁ h₂ := ⟨h₁.down.trans h₂.down⟩
  eqSub_refl _ _ _ := ⟨rfl⟩
  eqSub_symm _ _ _ _ h := ⟨h.down.symm⟩
  eqSub_trans _ _ _ _ _ h₁ h₂ := ⟨h₁.down.trans h₂.down⟩
  compSub_id_left _ _ _ := ⟨by simp⟩
  compSub_id_right _ _ _ := ⟨by simp⟩
  compSub_assoc _ _ _ _ _ _ _ := ⟨by simp⟩
  compSub_congr _ _ _ _ _ _ _ h₁ h₂ := ⟨by rw [h₁.down, h₂.down]⟩
  emptySub_eta Γ σ := ⟨toUnit_unique σ (toUnit Γ)⟩
  extendSub_weaken _ _ _ _ _ := ⟨by simp⟩
  extendSub_varZero _ _ _ _ _ := ⟨by simp⟩
  extendSub_eta _ _ _ σ := ⟨(CartesianMonoidalCategory.lift_comp_fst_snd σ).symm⟩
  extendSub_congr _ _ _ _ _ _ _ hσ ht := ⟨by rw [hσ.down, ht.down]⟩
  ctxToFrom _ := ⟨by simp⟩
  ctxFromTo _ := ⟨by ext; simp⟩
  subst_id _ _ _ := ⟨by simp⟩
  subst_comp _ _ _ _ _ _ _ := ⟨by simp⟩
  subst_congr _ _ _ _ _ _ _ hσ ht := ⟨by rw [hσ.down, ht.down]⟩
  subst_unit _ _ _ := ⟨by simp⟩
  subst_pair _ _ _ _ _ _ _ := ⟨by ext <;> simp⟩
  subst_fst _ _ _ _ _ _ := ⟨by simp⟩
  subst_snd _ _ _ _ _ _ := ⟨by simp⟩
  subst_lam Γ Δ A B σ body := ⟨by
    let body' : A ⊗ Δ ⟶ B := lift («snd» A Δ) («fst» A Δ) ≫ body
    rw [← MonoidalClosed.curry_natural_left σ body']
    congr 1
    dsimp [body']
    have h : A ◁ σ ≫ lift («snd» A Δ) («fst» A Δ) =
        lift («snd» A Γ) («fst» A Γ) ≫ lift («fst» Γ A ≫ σ) («snd» Γ A) := by
      ext <;> simp
    calc
      A ◁ σ ≫ lift («snd» A Δ) («fst» A Δ) ≫ body
          = (A ◁ σ ≫ lift («snd» A Δ) («fst» A Δ)) ≫ body := by
              rw [← Category.assoc]
      _   = (lift («snd» A Γ) («fst» A Γ) ≫ lift («fst» Γ A ≫ σ) («snd» Γ A)) ≫ body := by
              exact congrArg (fun f => f ≫ body) h
      _   = lift («snd» A Γ) («fst» A Γ) ≫ lift («fst» Γ A ≫ σ) («snd» Γ A) ≫ body := by
              rw [Category.assoc]⟩
  subst_app _ _ _ _ _ _ _ := ⟨by
    rw [← Category.assoc]
    congr 1
    ext <;> simp⟩
  prod_beta_fst _ _ _ _ _ := ⟨by simp⟩
  prod_beta_snd _ _ _ _ _ := ⟨by simp⟩
  prod_eta _ _ _ pair := ⟨(CartesianMonoidalCategory.lift_comp_fst_snd pair).symm⟩
  pair_congr _ _ _ _ _ _ _ hfst hsnd := ⟨by rw [hfst.down, hsnd.down]⟩
  fst_congr _ _ _ _ _ h := ⟨by rw [h.down]⟩
  snd_congr _ _ _ _ _ h := ⟨by rw [h.down]⟩
  beta Γ A B body arg := ⟨by
    let body' : A ⊗ Γ ⟶ B := lift («snd» A Γ) («fst» A Γ) ≫ body
    have hpair :
        lift arg (MonoidalClosed.curry body') =
          lift arg (𝟙 Γ) ≫ A ◁ MonoidalClosed.curry body' := by
      ext <;> simp
    have hsubst :
        lift arg (𝟙 Γ) ≫ (lift («snd» A Γ) («fst» A Γ) ≫ body) =
          lift (𝟙 Γ) arg ≫ body := by
      rw [← Category.assoc]
      congr 1
      ext <;> simp
    calc lift arg (MonoidalClosed.curry body') ≫ (ihom.ev A).app B
        = (lift arg (𝟙 Γ) ≫ A ◁ MonoidalClosed.curry body') ≫
            (ihom.ev A).app B := congrArg (fun f => f ≫ (ihom.ev A).app B) hpair
      _ = lift arg (𝟙 Γ) ≫ body' := by
            rw [Category.assoc]
            exact congrArg (fun f => lift arg (𝟙 Γ) ≫ f)
              (MonoidalClosed.whiskerLeft_curry_ihom_ev_app A B body')
      _   = lift (𝟙 Γ) arg ≫ body := hsubst⟩
  eta Γ A B fn := ⟨by
    have hwhisker : A ◁ fn = lift («fst» A Γ) («snd» A Γ ≫ fn) := by
      ext <;> simp
    have hcontext :
        lift («fst» A Γ) («snd» A Γ ≫ fn) =
          lift («snd» A Γ) («fst» A Γ) ≫ lift («snd» Γ A) («fst» Γ A ≫ fn) := by
      ext <;> simp
    conv_lhs => rw [← MonoidalClosed.curry_uncurry fn]
    congr 1
    calc MonoidalClosed.uncurry fn
        = A ◁ fn ≫ (ihom.ev A).app B := by rw [MonoidalClosed.uncurry_eq]
      _ = lift («fst» A Γ) («snd» A Γ ≫ fn) ≫ (ihom.ev A).app B := by rw [hwhisker]
      _ = lift («snd» A Γ) («fst» A Γ) ≫
          (lift («snd» Γ A) («fst» Γ A ≫ fn) ≫ (ihom.ev A).app B) := by
            rw [hcontext, Category.assoc]⟩
  lam_congr _ _ _ _ _ h := ⟨by rw [h.down]⟩
  app_congr _ _ _ _ _ _ _ hfn harg := ⟨by rw [hfn.down, harg.down]⟩
  unit_eta Γ t := ⟨toUnit_unique t (toUnit Γ)⟩

end CurryHowardLambekForward

section CurryHowardLambekBackward

abbrev LambdaCalculus.LambdaCalculusModel.category (M : LambdaCalculusModel) : Type := M.Ty

abbrev LambdaCalculus.LambdaCalculusModel.singletonCtx (M : LambdaCalculusModel)
    (A : M.Ty) : M.Ctx :=
  M.extendCtx M.emptyCtx A

def LambdaCalculus.LambdaCalculusModel.homSetoid (M : LambdaCalculusModel)
    (A B : M.Ty) : Setoid (M.Tm (M.singletonCtx A) B) where
  r t u := Nonempty (M.EqTm (M.singletonCtx A) B t u)
  iseqv :=
    { refl := fun t => ⟨M.eq_refl (M.singletonCtx A) B t⟩
      symm := fun h => ⟨M.eq_symm (M.singletonCtx A) B _ _ h.some⟩
      trans := fun h₁ h₂ => ⟨M.eq_trans (M.singletonCtx A) B _ _ _ h₁.some h₂.some⟩ }

abbrev LambdaCalculus.LambdaCalculusModel.Hom (M : LambdaCalculusModel)
    (A B : M.Ty) : Type :=
  Quotient (M.homSetoid A B)

abbrev LambdaCalculus.LambdaCalculusModel.homMk (M : LambdaCalculusModel) {A B : M.Ty}
    (t : M.Tm (M.singletonCtx A) B) : M.Hom A B :=
  Quotient.mk (M.homSetoid A B) t

lemma LambdaCalculus.LambdaCalculusModel.homMk_eq (M : LambdaCalculusModel) {A B : M.Ty}
    {t u : M.Tm (M.singletonCtx A) B} (h : M.EqTm (M.singletonCtx A) B t u) :
    M.homMk t = M.homMk u :=
  Quotient.sound ⟨h⟩

variable (M : LambdaCalculusModel)

/-- The derived weakening operation is reindexing along the weakening substitution. -/
def LambdaCalculus.LambdaCalculusModel.weakenTm_subst (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (B : M.Ty) (t : M.Tm Γ A) :
    M.EqTm (M.extendCtx Γ B) A (M.weakenTm Γ A B t)
      (M.substTm (M.extendCtx Γ B) Γ A (M.weakenSub Γ B) t) :=
  M.eq_refl (M.extendCtx Γ B) A _

/-- The derived top-substitution operation is explicit substitution by an extended identity. -/
def LambdaCalculus.LambdaCalculusModel.substTop_subst (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (B : M.Ty)
    (body : M.Tm (M.extendCtx Γ A) B) (arg : M.Tm Γ A) :
    M.EqTm Γ B (M.substTop Γ A B body arg)
      (M.substTm Γ (M.extendCtx Γ A) B (M.extendSub Γ Γ A (M.idSub Γ) arg) body) :=
  M.eq_refl Γ B _

/-- The newest variable substitutes to the argument. -/
def LambdaCalculus.LambdaCalculusModel.subst_var_zero (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (arg : M.Tm Γ A) :
    M.EqTm Γ A (M.substTop Γ A A (M.varZero Γ A) arg) arg :=
  M.eq_trans Γ A _ _ _
    (M.substTop_subst Γ A A (M.varZero Γ A) arg)
    (M.extendSub_varZero Γ Γ A (M.idSub Γ) arg)

/-- The substitution into a singleton context classified by a term. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A : M.Ty} (t : M.Tm Γ A) : M.Sub Γ (M.singletonCtx A) :=
  M.extendSub Γ M.emptyCtx A (M.emptySub Γ) t

/-- Congruence for substitutions into a singleton context. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub_congr (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A : M.Ty} {t u : M.Tm Γ A} (h : M.EqTm Γ A t u) :
    M.EqSub Γ (M.singletonCtx A) (M.singletonSub t) (M.singletonSub u) :=
  M.extendSub_congr Γ M.emptyCtx A (M.emptySub Γ) (M.emptySub Γ) t u
    (M.eqSub_refl Γ M.emptyCtx (M.emptySub Γ)) h

/-- The variable of a singleton context reindexed along its classifying substitution. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub_var (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A : M.Ty} (t : M.Tm Γ A) :
    M.EqTm Γ A
      (M.substTm Γ (M.singletonCtx A) A (M.singletonSub t) (M.varZero M.emptyCtx A)) t :=
  M.extendSub_varZero Γ M.emptyCtx A (M.emptySub Γ) t

/-- Eta-expansion for substitutions into singleton contexts. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub_eta (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A : M.Ty} (σ : M.Sub Γ (M.singletonCtx A)) :
    M.EqSub Γ (M.singletonCtx A) σ
      (M.singletonSub (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A))) :=
  M.eqSub_trans Γ (M.singletonCtx A) σ
    (M.extendSub Γ M.emptyCtx A
      (M.compSub Γ (M.singletonCtx A) M.emptyCtx σ (M.weakenSub M.emptyCtx A))
      (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A)))
    (M.singletonSub (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A)))
    (M.extendSub_eta Γ M.emptyCtx A σ)
    (M.extendSub_congr Γ M.emptyCtx A
      (M.compSub Γ (M.singletonCtx A) M.emptyCtx σ (M.weakenSub M.emptyCtx A))
      (M.emptySub Γ)
      (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A))
      (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A))
      (M.emptySub_eta Γ
        (M.compSub Γ (M.singletonCtx A) M.emptyCtx σ (M.weakenSub M.emptyCtx A)))
      (M.eq_refl Γ A _))

/-- Extensionality for substitutions into singleton contexts. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub_ext (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A : M.Ty} {σ τ : M.Sub Γ (M.singletonCtx A)}
    (h : M.EqTm Γ A
      (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A))
      (M.substTm Γ (M.singletonCtx A) A τ (M.varZero M.emptyCtx A))) :
    M.EqSub Γ (M.singletonCtx A) σ τ :=
  M.eqSub_trans Γ (M.singletonCtx A) σ
    (M.singletonSub (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A))) τ
    (M.singletonSub_eta σ)
    (M.eqSub_trans Γ (M.singletonCtx A)
      (M.singletonSub (M.substTm Γ (M.singletonCtx A) A σ (M.varZero M.emptyCtx A)))
      (M.singletonSub (M.substTm Γ (M.singletonCtx A) A τ (M.varZero M.emptyCtx A))) τ
      (M.singletonSub_congr h)
      (M.eqSub_symm Γ (M.singletonCtx A) τ
        (M.singletonSub (M.substTm Γ (M.singletonCtx A) A τ (M.varZero M.emptyCtx A)))
        (M.singletonSub_eta τ)))

/-- Composition with a singleton-context substitution, evaluated on the singleton variable. -/
def LambdaCalculus.LambdaCalculusModel.subst_comp_singleton_var (M : LambdaCalculusModel)
    {Γ Δ : M.Ctx} {A : M.Ty} (σ : M.Sub Γ Δ) (t : M.Tm Δ A) :
    M.EqTm Γ A
      (M.substTm Γ (M.singletonCtx A) A
        (M.compSub Γ Δ (M.singletonCtx A) σ (M.singletonSub t))
        (M.varZero M.emptyCtx A))
      (M.substTm Γ Δ A σ t) :=
  M.eq_trans Γ A _ _ _
    (M.subst_comp Γ Δ (M.singletonCtx A) A σ (M.singletonSub t) (M.varZero M.emptyCtx A))
    (M.subst_congr Γ Δ A σ σ
      (M.substTm Δ (M.singletonCtx A) A (M.singletonSub t) (M.varZero M.emptyCtx A)) t
      (M.eqSub_refl Γ Δ σ) (M.singletonSub_var t))

/-- Composition with a singleton-context substitution is classified by substituting its
classifier. -/
def LambdaCalculus.LambdaCalculusModel.singletonSub_comp (M : LambdaCalculusModel)
    {Γ Δ : M.Ctx} {A : M.Ty} (σ : M.Sub Γ Δ) (t : M.Tm Δ A) :
    M.EqSub Γ (M.singletonCtx A)
      (M.compSub Γ Δ (M.singletonCtx A) σ (M.singletonSub t))
      (M.singletonSub (M.substTm Γ Δ A σ t)) :=
  M.singletonSub_ext (M.eq_trans Γ A _ _ _
    (M.subst_comp_singleton_var σ t)
    (M.eq_symm Γ A _ _ (M.singletonSub_var (M.substTm Γ Δ A σ t))))

/-- One-variable composition agrees with explicit substitution into a singleton context. -/
def LambdaCalculus.LambdaCalculusModel.homComp_subst (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Tm (M.singletonCtx A) B)
    (g : M.Tm (M.singletonCtx B) C) :
    M.EqTm (M.singletonCtx A) C (M.homComp A B C f g)
      (M.substTm (M.singletonCtx A) (M.singletonCtx B) C (M.singletonSub f) g) :=
  M.eq_refl (M.singletonCtx A) C _

/-- Congruence for one-variable composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_congr (M : LambdaCalculusModel)
    (A B C : M.Ty)
    (f₁ : M.Tm (M.singletonCtx A) B) (f₂ : M.Tm (M.singletonCtx A) B)
    (g₁ : M.Tm (M.singletonCtx B) C) (g₂ : M.Tm (M.singletonCtx B) C)
    (f_eq : M.EqTm (M.singletonCtx A) B f₁ f₂)
    (g_eq : M.EqTm (M.singletonCtx B) C g₁ g₂) :
    M.EqTm (M.singletonCtx A) C (M.homComp A B C f₁ g₁) (M.homComp A B C f₂ g₂) :=
  M.eq_trans (M.singletonCtx A) C _ _ _
    (M.homComp_subst A B C f₁ g₁)
    (M.eq_trans (M.singletonCtx A) C _ _ _
      (M.subst_congr (M.singletonCtx A) (M.singletonCtx B) C
        (M.singletonSub f₁) (M.singletonSub f₂) g₁ g₂
        (M.singletonSub_congr f_eq) g_eq)
      (M.eq_symm (M.singletonCtx A) C _ _ (M.homComp_subst A B C f₂ g₂)))

/-- Right identity for one-variable composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_id_right (M : LambdaCalculusModel)
    (A B : M.Ty) (f : M.Tm (M.singletonCtx A) B) :
    M.EqTm (M.singletonCtx A) B (M.homComp A B B f (M.varZero M.emptyCtx B)) f :=
  M.eq_trans (M.singletonCtx A) B _ _ _
    (M.homComp_subst A B B f (M.varZero M.emptyCtx B))
    (M.singletonSub_var f)

/-- Left identity for one-variable composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_id_left (M : LambdaCalculusModel)
    (A B : M.Ty) (f : M.Tm (M.singletonCtx A) B) :
    M.EqTm (M.singletonCtx A) B (M.homComp A A B (M.varZero M.emptyCtx A) f) f :=
  let ΓA := M.singletonCtx A
  let σ : M.Sub ΓA ΓA := M.singletonSub (M.varZero M.emptyCtx A)
  let hIdSubst : M.EqSub ΓA ΓA (M.idSub ΓA)
      (M.singletonSub (M.substTm ΓA ΓA A (M.idSub ΓA) (M.varZero M.emptyCtx A))) :=
    M.singletonSub_eta (M.idSub ΓA)
  let hIdVar : M.EqSub ΓA ΓA
      (M.singletonSub (M.substTm ΓA ΓA A (M.idSub ΓA) (M.varZero M.emptyCtx A))) σ :=
    M.singletonSub_congr (M.subst_id ΓA A (M.varZero M.emptyCtx A))
  let hσ : M.EqSub ΓA ΓA σ (M.idSub ΓA) :=
    M.eqSub_symm ΓA ΓA (M.idSub ΓA) σ (M.eqSub_trans ΓA ΓA (M.idSub ΓA)
      (M.singletonSub (M.substTm ΓA ΓA A (M.idSub ΓA) (M.varZero M.emptyCtx A))) σ
      hIdSubst hIdVar)
  M.eq_trans ΓA B _ _ _
    (M.homComp_subst A A B (M.varZero M.emptyCtx A) f)
    (M.eq_trans ΓA B _ _ _
      (M.subst_congr ΓA ΓA B σ (M.idSub ΓA) f f hσ (M.eq_refl ΓA B f))
      (M.subst_id ΓA B f))

/-- Associativity for one-variable composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_assoc (M : LambdaCalculusModel)
    (A B C D : M.Ty)
    (f : M.Tm (M.singletonCtx A) B)
    (g : M.Tm (M.singletonCtx B) C)
    (h : M.Tm (M.singletonCtx C) D) :
    M.EqTm (M.singletonCtx A) D
      (M.homComp A C D (M.homComp A B C f g) h)
      (M.homComp A B D f (M.homComp B C D g h)) :=
  let ΓA := M.singletonCtx A
  let ΓB := M.singletonCtx B
  let ΓC := M.singletonCtx C
  let σf : M.Sub ΓA ΓB := M.singletonSub f
  let σg : M.Sub ΓB ΓC := M.singletonSub g
  let σfg : M.Sub ΓA ΓC := M.singletonSub (M.homComp A B C f g)
  let hσ : M.EqSub ΓA ΓC σfg (M.compSub ΓA ΓB ΓC σf σg) :=
    M.eqSub_trans ΓA ΓC σfg
      (M.singletonSub (M.substTm ΓA ΓB C σf g)) (M.compSub ΓA ΓB ΓC σf σg)
      (M.singletonSub_congr (M.homComp_subst A B C f g))
      (M.eqSub_symm ΓA ΓC (M.compSub ΓA ΓB ΓC σf σg)
        (M.singletonSub (M.substTm ΓA ΓB C σf g))
        (M.singletonSub_comp σf g))
  M.eq_trans ΓA D _ _ _
    (M.homComp_subst A C D (M.homComp A B C f g) h)
    (M.eq_trans ΓA D _ _ _
      (M.subst_congr ΓA ΓC D σfg (M.compSub ΓA ΓB ΓC σf σg) h h
        hσ (M.eq_refl ΓC D h))
      (M.eq_trans ΓA D _ _ _
        (M.subst_comp ΓA ΓB ΓC D σf σg h)
        (M.eq_trans ΓA D _ _ _
          (M.subst_congr ΓA ΓB D σf σf
            (M.substTm ΓB ΓC D σg h) (M.homComp B C D g h)
            (M.eqSub_refl ΓA ΓB σf)
            (M.eq_symm ΓB D _ _ (M.homComp_subst B C D g h)))
          (M.eq_symm ΓA D _ _ (M.homComp_subst A B D f (M.homComp B C D g h))))))

/-- One-variable composition preserves product pairing. -/
def LambdaCalculus.LambdaCalculusModel.homComp_pair (M : LambdaCalculusModel)
    (A B C D : M.Ty)
    (f : M.Tm (M.singletonCtx A) B)
    (g : M.Tm (M.singletonCtx B) C)
    (h : M.Tm (M.singletonCtx B) D) :
    M.EqTm (M.singletonCtx A) (M.prodTy C D)
      (M.homComp A B (M.prodTy C D) f (M.pairTm (M.singletonCtx B) C D g h))
      (M.pairTm (M.singletonCtx A) C D (M.homComp A B C f g) (M.homComp A B D f h)) :=
  let σ : M.Sub (M.singletonCtx A) (M.singletonCtx B) := M.singletonSub f
  M.eq_trans (M.singletonCtx A) (M.prodTy C D) _ _ _
    (M.homComp_subst A B (M.prodTy C D) f (M.pairTm (M.singletonCtx B) C D g h))
    (M.eq_trans (M.singletonCtx A) (M.prodTy C D) _ _ _
      (M.subst_pair (M.singletonCtx A) (M.singletonCtx B) C D σ g h)
      (M.pair_congr (M.singletonCtx A) C D _ _ _ _
        (M.eq_symm (M.singletonCtx A) C _ _ (M.homComp_subst A B C f g))
        (M.eq_symm (M.singletonCtx A) D _ _ (M.homComp_subst A B D f h))))

/-- One-variable composition with a first projection is first projection after composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_fst (M : LambdaCalculusModel)
    (A B C : M.Ty) (p : M.Tm (M.singletonCtx A) (M.prodTy B C)) :
    M.EqTm (M.singletonCtx A) B
      (M.homComp A (M.prodTy B C) B p
        (M.fstTm (M.singletonCtx (M.prodTy B C)) B C
          (M.varZero M.emptyCtx (M.prodTy B C))))
      (M.fstTm (M.singletonCtx A) B C p) :=
  let ΓA := M.singletonCtx A
  let ΓP := M.singletonCtx (M.prodTy B C)
  let prodVar : M.Tm ΓP (M.prodTy B C) := M.varZero M.emptyCtx (M.prodTy B C)
  let σ : M.Sub ΓA ΓP := M.singletonSub p
  M.eq_trans ΓA B _ _ _
    (M.homComp_subst A (M.prodTy B C) B p (M.fstTm ΓP B C prodVar))
    (M.eq_trans ΓA B _ _ _
      (M.subst_fst ΓA ΓP B C σ prodVar)
      (M.fst_congr ΓA B C _ _ (M.singletonSub_var p)))

/-- One-variable composition with a second projection is second projection after composition. -/
def LambdaCalculus.LambdaCalculusModel.homComp_snd (M : LambdaCalculusModel)
    (A B C : M.Ty) (p : M.Tm (M.singletonCtx A) (M.prodTy B C)) :
    M.EqTm (M.singletonCtx A) C
      (M.homComp A (M.prodTy B C) C p
        (M.sndTm (M.singletonCtx (M.prodTy B C)) B C
          (M.varZero M.emptyCtx (M.prodTy B C))))
      (M.sndTm (M.singletonCtx A) B C p) :=
  let ΓA := M.singletonCtx A
  let ΓP := M.singletonCtx (M.prodTy B C)
  let prodVar : M.Tm ΓP (M.prodTy B C) := M.varZero M.emptyCtx (M.prodTy B C)
  let σ : M.Sub ΓA ΓP := M.singletonSub p
  M.eq_trans ΓA C _ _ _
    (M.homComp_subst A (M.prodTy B C) C p (M.sndTm ΓP B C prodVar))
    (M.eq_trans ΓA C _ _ _
      (M.subst_snd ΓA ΓP B C σ prodVar)
      (M.snd_congr ΓA B C _ _ (M.singletonSub_var p)))

/-- The syntactic category of types and one-variable terms modulo definitional equality. -/
instance : Category M.category where
  Hom A B := M.Hom A B
  id A := Quotient.mk (M.homSetoid A A) (M.varZero M.emptyCtx A)
  comp {A B C} f g :=
    Quotient.liftOn₂ f g
      (fun f g => Quotient.mk (M.homSetoid A C) (M.homComp A B C f g))
      (by
        intro f₁ g₁ f₂ g₂ hf hg
        exact Quotient.sound ⟨M.homComp_congr A B C f₁ f₂ g₁ g₂ hf.some hg.some⟩)
  id_comp := by
    intro A B f
    exact Quotient.inductionOn f fun f =>
      Quotient.sound ⟨M.homComp_id_left A B f⟩
  comp_id := by
    intro A B f
    exact Quotient.inductionOn f fun f =>
      Quotient.sound ⟨M.homComp_id_right A B f⟩
  assoc := by
    intro A B C D f g h
    exact Quotient.inductionOn f fun f =>
      Quotient.inductionOn g fun g =>
        Quotient.inductionOn h fun h =>
          Quotient.sound ⟨M.homComp_assoc A B C D f g h⟩

/-- The unique syntactic morphism to the unit type. -/
def LambdaCalculus.LambdaCalculusModel.terminalHom (M : LambdaCalculusModel)
    (A : M.Ty) : M.Hom A M.unitTy :=
  M.homMk (M.unitIntro (M.singletonCtx A))

/-- The unit type is terminal in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.terminalLimitCone (M : LambdaCalculusModel) :
    LimitCone (Functor.empty.{0} M.category) where
  cone := asEmptyCone M.unitTy
  isLimit := IsTerminal.ofUniqueHom (fun A => M.terminalHom A) (by
    intro A m
    exact Quotient.inductionOn m fun t =>
      Quotient.sound ⟨M.unit_eta (M.singletonCtx A) t⟩)

/-- First projection from the syntactic product type. -/
def LambdaCalculus.LambdaCalculusModel.prodFst (M : LambdaCalculusModel)
    (A B : M.Ty) : M.Hom (M.prodTy A B) A :=
  M.homMk (M.fstTm (M.singletonCtx (M.prodTy A B)) A B
    (M.varZero M.emptyCtx (M.prodTy A B)))

/-- Second projection from the syntactic product type. -/
def LambdaCalculus.LambdaCalculusModel.prodSnd (M : LambdaCalculusModel)
    (A B : M.Ty) : M.Hom (M.prodTy A B) B :=
  M.homMk (M.sndTm (M.singletonCtx (M.prodTy A B)) A B
    (M.varZero M.emptyCtx (M.prodTy A B)))

/-- Pairing into the syntactic product type. -/
def LambdaCalculus.LambdaCalculusModel.prodLift (M : LambdaCalculusModel) {T A B : M.Ty}
    (f : M.Hom T A) (g : M.Hom T B) : M.Hom T (M.prodTy A B) :=
  Quotient.liftOn₂ f g
    (fun f g => M.homMk (M.pairTm (M.singletonCtx T) A B f g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      exact M.homMk_eq
        (M.pair_congr (M.singletonCtx T) A B f₁ f₂ g₁ g₂ hf.some hg.some))

/-- The product type is a categorical binary product in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.productLimitCone (M : LambdaCalculusModel)
    (A B : M.Ty) : LimitCone (pair A B) where
  cone := BinaryFan.mk (M.prodFst A B) (M.prodSnd A B)
  isLimit := BinaryFan.IsLimit.mk _
    (fun f g => M.prodLift f g)
    (by
      intro T f g
      exact Quotient.inductionOn f fun f =>
        Quotient.inductionOn g fun g => by
          simp [prodLift, prodFst, homMk, CategoryStruct.comp]
          exact Quotient.sound ⟨M.eq_trans (M.singletonCtx T) A _ _ _
            (M.homComp_fst T A B (M.pairTm (M.singletonCtx T) A B f g))
            (M.prod_beta_fst (M.singletonCtx T) A B f g)⟩)
    (by
      intro T f g
      exact Quotient.inductionOn f fun f =>
        Quotient.inductionOn g fun g => by
          simp [prodLift, prodSnd, homMk, CategoryStruct.comp]
          exact Quotient.sound ⟨M.eq_trans (M.singletonCtx T) B _ _ _
            (M.homComp_snd T A B (M.pairTm (M.singletonCtx T) A B f g))
            (M.prod_beta_snd (M.singletonCtx T) A B f g)⟩)
    (by
      intro T f g m hf hg
      rw [← hf, ← hg]
      exact Quotient.inductionOn m fun m => by
        simp [prodLift, prodFst, prodSnd, homMk, CategoryStruct.comp]
        exact Quotient.sound ⟨M.eq_trans (M.singletonCtx T) (M.prodTy A B) _ _ _
          (M.prod_eta (M.singletonCtx T) A B m)
          (M.pair_congr (M.singletonCtx T) A B _ _ _ _
            (M.eq_symm (M.singletonCtx T) A _ _ (M.homComp_fst T A B m))
            (M.eq_symm (M.singletonCtx T) B _ _ (M.homComp_snd T A B m)))⟩)

/-- Finite products make the syntactic category cartesian monoidal. -/
instance : CartesianMonoidalCategory M.category :=
  CartesianMonoidalCategory.ofChosenFiniteProducts M.terminalLimitCone M.productLimitCone

/-- Reindexing the first projection of a singleton product classified by a pair. -/
def LambdaCalculus.LambdaCalculusModel.subst_fst_pair (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A B : M.Ty} (p : M.Tm Γ A) (q : M.Tm Γ B) :
    M.EqTm Γ A
      (M.substTm Γ (M.singletonCtx (M.prodTy A B)) A
        (M.singletonSub (M.pairTm Γ A B p q))
        (M.fstTm (M.singletonCtx (M.prodTy A B)) A B
          (M.varZero M.emptyCtx (M.prodTy A B))))
      p :=
  M.eq_trans Γ A _ _ _
    (M.subst_fst Γ (M.singletonCtx (M.prodTy A B)) A B
      (M.singletonSub (M.pairTm Γ A B p q)) (M.varZero M.emptyCtx (M.prodTy A B)))
    (M.eq_trans Γ A _ _ _
      (M.fst_congr Γ A B _ _ (M.singletonSub_var (M.pairTm Γ A B p q)))
      (M.prod_beta_fst Γ A B p q))

/-- Reindexing the second projection of a singleton product classified by a pair. -/
def LambdaCalculus.LambdaCalculusModel.subst_snd_pair (M : LambdaCalculusModel)
    {Γ : M.Ctx} {A B : M.Ty} (p : M.Tm Γ A) (q : M.Tm Γ B) :
    M.EqTm Γ B
      (M.substTm Γ (M.singletonCtx (M.prodTy A B)) B
        (M.singletonSub (M.pairTm Γ A B p q))
        (M.sndTm (M.singletonCtx (M.prodTy A B)) A B
          (M.varZero M.emptyCtx (M.prodTy A B))))
      q :=
  M.eq_trans Γ B _ _ _
    (M.subst_snd Γ (M.singletonCtx (M.prodTy A B)) A B
      (M.singletonSub (M.pairTm Γ A B p q)) (M.varZero M.emptyCtx (M.prodTy A B)))
    (M.eq_trans Γ B _ _ _
      (M.snd_congr Γ A B _ _ (M.singletonSub_var (M.pairTm Γ A B p q)))
      (M.prod_beta_snd Γ A B p q))

/-- Substitution distributes over one-variable composition. -/
def LambdaCalculus.LambdaCalculusModel.subst_homComp (M : LambdaCalculusModel)
    {Γ : M.Ctx} (A B C : M.Ty) (σ : M.Sub Γ (M.singletonCtx A))
    (f : M.Tm (M.singletonCtx A) B) (g : M.Tm (M.singletonCtx B) C) :
    M.EqTm Γ C
      (M.substTm Γ (M.singletonCtx A) C σ (M.homComp A B C f g))
      (M.substTm Γ (M.singletonCtx B) C
        (M.singletonSub (M.substTm Γ (M.singletonCtx A) B σ f)) g) :=
  M.eq_trans Γ C _ _ _
    (M.subst_congr Γ (M.singletonCtx A) C σ σ (M.homComp A B C f g)
      (M.substTm (M.singletonCtx A) (M.singletonCtx B) C (M.singletonSub f) g)
      (M.eqSub_refl Γ (M.singletonCtx A) σ) (M.homComp_subst A B C f g))
    (M.eq_trans Γ C _ _ _
      (M.eq_symm Γ C _ _
        (M.subst_comp Γ (M.singletonCtx A) (M.singletonCtx B) C σ (M.singletonSub f) g))
      (M.subst_congr Γ (M.singletonCtx B) C
        (M.compSub Γ (M.singletonCtx A) (M.singletonCtx B) σ (M.singletonSub f))
        (M.singletonSub (M.substTm Γ (M.singletonCtx A) B σ f)) g g
        (M.singletonSub_comp σ f) (M.eq_refl (M.singletonCtx B) C g)))

/-- Term-level currying for one-variable morphisms in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.curryTerm (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Tm (M.singletonCtx (M.prodTy A B)) C) :
    M.Tm (M.singletonCtx B) (M.arrowTy A C) :=
  M.lam (M.singletonCtx B) A C
    (M.substTm (M.extendCtx (M.singletonCtx B) A) (M.singletonCtx (M.prodTy A B)) C
      (M.singletonSub
        (M.pairTm (M.extendCtx (M.singletonCtx B) A) A B
          (M.varZero (M.singletonCtx B) A)
          (M.weakenTm (M.singletonCtx B) B A (M.varZero M.emptyCtx B))))
      f)

/-- Term-level uncurrying for one-variable morphisms in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.uncurryTerm (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Tm (M.singletonCtx B) (M.arrowTy A C)) :
    M.Tm (M.singletonCtx (M.prodTy A B)) C :=
  M.app (M.singletonCtx (M.prodTy A B)) A C
    (M.substTm (M.singletonCtx (M.prodTy A B)) (M.singletonCtx B) (M.arrowTy A C)
      (M.singletonSub
        (M.sndTm (M.singletonCtx (M.prodTy A B)) A B
          (M.varZero M.emptyCtx (M.prodTy A B))))
      f)
    (M.fstTm (M.singletonCtx (M.prodTy A B)) A B
      (M.varZero M.emptyCtx (M.prodTy A B)))

/-- Reindexing an uncurried term along a pair. -/
def LambdaCalculus.LambdaCalculusModel.subst_uncurryTerm_pair (M : LambdaCalculusModel)
    {Γ : M.Ctx} (A B C : M.Ty) (p : M.Tm Γ A) (q : M.Tm Γ B)
    (f : M.Tm (M.singletonCtx B) (M.arrowTy A C)) :
    M.EqTm Γ C
      (M.substTm Γ (M.singletonCtx (M.prodTy A B)) C
        (M.singletonSub (M.pairTm Γ A B p q)) (M.uncurryTerm A B C f))
      (M.app Γ A C
        (M.substTm Γ (M.singletonCtx B) (M.arrowTy A C) (M.singletonSub q) f) p) := by
  let σPair : M.Sub Γ (M.singletonCtx (M.prodTy A B)) := M.singletonSub (M.pairTm Γ A B p q)
  let ΓProd := M.singletonCtx (M.prodTy A B)
  let prodVar : M.Tm ΓProd (M.prodTy A B) := M.varZero M.emptyCtx (M.prodTy A B)
  let sndProd : M.Tm ΓProd B := M.sndTm ΓProd A B prodVar
  let σSnd : M.Sub ΓProd (M.singletonCtx B) := M.singletonSub sndProd
  let fstProd : M.Tm ΓProd A := M.fstTm ΓProd A B prodVar
  let harg : M.EqTm Γ A (M.substTm Γ ΓProd A σPair fstProd) p :=
    M.subst_fst_pair p q
  let hcompSnd : M.EqSub Γ (M.singletonCtx B)
      (M.compSub Γ ΓProd (M.singletonCtx B) σPair σSnd) (M.singletonSub q) := by
    apply M.singletonSub_ext
    exact M.eq_trans Γ B _ _ _
      (M.subst_comp_singleton_var σPair sndProd)
      (M.eq_trans Γ B _ _ _
        (M.subst_snd_pair p q)
        (M.eq_symm Γ B _ _ (M.singletonSub_var q)))
  let hfn : M.EqTm Γ (M.arrowTy A C)
      (M.substTm Γ ΓProd (M.arrowTy A C) σPair
        (M.substTm ΓProd (M.singletonCtx B) (M.arrowTy A C) σSnd f))
      (M.substTm Γ (M.singletonCtx B) (M.arrowTy A C) (M.singletonSub q) f) :=
    M.eq_trans Γ (M.arrowTy A C) _ _ _
      (M.eq_symm Γ (M.arrowTy A C) _ _
        (M.subst_comp Γ ΓProd (M.singletonCtx B) (M.arrowTy A C) σPair σSnd f))
      (M.subst_congr Γ (M.singletonCtx B) (M.arrowTy A C)
        (M.compSub Γ ΓProd (M.singletonCtx B) σPair σSnd) (M.singletonSub q) f f
        hcompSnd (M.eq_refl (M.singletonCtx B) (M.arrowTy A C) f))
  exact M.eq_trans Γ C _ _ _
    (M.subst_app Γ ΓProd A C σPair
      (M.substTm ΓProd (M.singletonCtx B) (M.arrowTy A C) σSnd f) fstProd)
    (M.app_congr Γ A C _ _ _ _ hfn harg)

/-- Term-level `curry (uncurry g) = g`, derived from function η and substitution laws. -/
def LambdaCalculus.LambdaCalculusModel.curry_uncurryTerm (M : LambdaCalculusModel)
    (A B C : M.Ty) (g : M.Tm (M.singletonCtx B) (M.arrowTy A C)) :
    M.EqTm (M.singletonCtx B) (M.arrowTy A C)
      (M.curryTerm A B C (M.uncurryTerm A B C g)) g := by
  let ΓB := M.singletonCtx B
  let ΓBA := M.extendCtx ΓB A
  let ΓProd := M.singletonCtx (M.prodTy A B)
  let varA : M.Tm ΓBA A := M.varZero ΓB A
  let varB : M.Tm ΓB B := M.varZero M.emptyCtx B
  let weakB : M.Tm ΓBA B := M.weakenTm ΓB B A varB
  let pairAB : M.Tm ΓBA (M.prodTy A B) := M.pairTm ΓBA A B varA weakB
  let σPair : M.Sub ΓBA ΓProd := M.singletonSub pairAB
  let prodVar : M.Tm ΓProd (M.prodTy A B) := M.varZero M.emptyCtx (M.prodTy A B)
  let sndProd : M.Tm ΓProd B := M.sndTm ΓProd A B prodVar
  let σSnd : M.Sub ΓProd ΓB := M.singletonSub sndProd
  let fstProd : M.Tm ΓProd A := M.fstTm ΓProd A B prodVar
  let harg : M.EqTm ΓBA A (M.substTm ΓBA ΓProd A σPair fstProd) varA := by
    exact M.subst_fst_pair varA weakB
  let hcompSnd : M.EqSub ΓBA ΓB (M.compSub ΓBA ΓProd ΓB σPair σSnd)
      (M.weakenSub ΓB A) := by
    apply M.singletonSub_ext
    exact M.eq_trans ΓBA B _ _ _
      (M.subst_comp_singleton_var σPair sndProd)
      (M.eq_trans ΓBA B _ _ _
        (M.subst_snd_pair varA weakB)
        (M.weakenTm_subst ΓB B A varB))
  let hfn : M.EqTm ΓBA (M.arrowTy A C)
      (M.substTm ΓBA ΓProd (M.arrowTy A C) σPair
        (M.substTm ΓProd ΓB (M.arrowTy A C) σSnd g))
      (M.weakenTm ΓB (M.arrowTy A C) A g) :=
    M.eq_trans ΓBA (M.arrowTy A C) _ _ _
      (M.eq_symm ΓBA (M.arrowTy A C) _ _
        (M.subst_comp ΓBA ΓProd ΓB (M.arrowTy A C) σPair σSnd g))
      (M.eq_trans ΓBA (M.arrowTy A C) _ _ _
        (M.subst_congr ΓBA ΓB (M.arrowTy A C)
          (M.compSub ΓBA ΓProd ΓB σPair σSnd) (M.weakenSub ΓB A) g g
          hcompSnd (M.eq_refl ΓB (M.arrowTy A C) g))
        (M.eq_symm ΓBA (M.arrowTy A C) _ _
          (M.weakenTm_subst ΓB (M.arrowTy A C) A g)))
  let hbody : M.EqTm ΓBA C
      (M.substTm ΓBA ΓProd C σPair (M.uncurryTerm A B C g))
      (M.app ΓBA A C (M.weakenTm ΓB (M.arrowTy A C) A g) varA) :=
    M.eq_trans ΓBA C _ _ _
      (M.subst_app ΓBA ΓProd A C σPair
        (M.substTm ΓProd ΓB (M.arrowTy A C) σSnd g) fstProd)
      (M.app_congr ΓBA A C _ _ _ _ hfn harg)
  exact M.eq_trans ΓB (M.arrowTy A C) _ _ _
    (M.lam_congr ΓB A C _ _ hbody)
    (M.eq_symm ΓB (M.arrowTy A C) _ _ (M.eta ΓB A C g))

/-- Term-level `uncurry (curry f) = f`, derived from function β and product η. -/
def LambdaCalculus.LambdaCalculusModel.uncurry_curryTerm (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Tm (M.singletonCtx (M.prodTy A B)) C) :
    M.EqTm (M.singletonCtx (M.prodTy A B)) C
      (M.uncurryTerm A B C (M.curryTerm A B C f)) f := by
  let ΓP := M.singletonCtx (M.prodTy A B)
  let ΓB := M.singletonCtx B
  let ΓBA := M.extendCtx ΓB A
  let ΓPA := M.extendCtx ΓP A
  let prodVar : M.Tm ΓP (M.prodTy A B) := M.varZero M.emptyCtx (M.prodTy A B)
  let fstP : M.Tm ΓP A := M.fstTm ΓP A B prodVar
  let sndP : M.Tm ΓP B := M.sndTm ΓP A B prodVar
  let σSnd : M.Sub ΓP ΓB := M.singletonSub sndP
  let varA_BA : M.Tm ΓBA A := M.varZero ΓB A
  let varB : M.Tm ΓB B := M.varZero M.emptyCtx B
  let weakB : M.Tm ΓBA B := M.weakenTm ΓB B A varB
  let pairAB : M.Tm ΓBA (M.prodTy A B) := M.pairTm ΓBA A B varA_BA weakB
  let σPair : M.Sub ΓBA ΓP := M.singletonSub pairAB
  let body : M.Tm ΓBA C := M.substTm ΓBA ΓP C σPair f
  let τTop : M.Sub ΓP ΓPA := M.extendSub ΓP ΓP A (M.idSub ΓP) fstP
  let σUnder : M.Sub ΓPA ΓBA :=
    M.extendSub ΓPA ΓB A
      (M.compSub ΓPA ΓP ΓB (M.weakenSub ΓP A) σSnd)
      (M.varZero ΓP A)
  let compUnder : M.Sub ΓP ΓBA := M.compSub ΓP ΓPA ΓBA τTop σUnder
  let hA : M.EqTm ΓP A (M.substTm ΓP ΓBA A compUnder varA_BA) fstP :=
    M.eq_trans ΓP A _ _ _
      (M.subst_comp ΓP ΓPA ΓBA A τTop σUnder varA_BA)
      (M.eq_trans ΓP A _ _ _
        (M.subst_congr ΓP ΓPA A τTop τTop
          (M.substTm ΓPA ΓBA A σUnder varA_BA) (M.varZero ΓP A)
          (M.eqSub_refl ΓP ΓPA τTop)
          (M.extendSub_varZero ΓPA ΓB A
            (M.compSub ΓPA ΓP ΓB (M.weakenSub ΓP A) σSnd)
            (M.varZero ΓP A)))
        (M.extendSub_varZero ΓP ΓP A (M.idSub ΓP) fstP))
  let hSubB : M.EqSub ΓP ΓB
      (M.compSub ΓP ΓBA ΓB compUnder (M.weakenSub ΓB A)) σSnd := by
    let baseUnder : M.Sub ΓPA ΓB := M.compSub ΓPA ΓP ΓB (M.weakenSub ΓP A) σSnd
    let left1 : M.Sub ΓP ΓB := M.compSub ΓP ΓBA ΓB compUnder (M.weakenSub ΓB A)
    let left2 : M.Sub ΓP ΓB := M.compSub ΓP ΓPA ΓB τTop
      (M.compSub ΓPA ΓBA ΓB σUnder (M.weakenSub ΓB A))
    let left3 : M.Sub ΓP ΓB := M.compSub ΓP ΓPA ΓB τTop baseUnder
    let left4 : M.Sub ΓP ΓB := M.compSub ΓP ΓP ΓB
      (M.compSub ΓP ΓPA ΓP τTop (M.weakenSub ΓP A)) σSnd
    let left5 : M.Sub ΓP ΓB := M.compSub ΓP ΓP ΓB (M.idSub ΓP) σSnd
    exact M.eqSub_trans ΓP ΓB left1 left2 σSnd
      (M.compSub_assoc ΓP ΓPA ΓBA ΓB τTop σUnder (M.weakenSub ΓB A))
      (M.eqSub_trans ΓP ΓB left2 left3 σSnd
        (M.compSub_congr ΓP ΓPA ΓB τTop τTop
          (M.compSub ΓPA ΓBA ΓB σUnder (M.weakenSub ΓB A)) baseUnder
          (M.eqSub_refl ΓP ΓPA τTop)
          (M.extendSub_weaken ΓPA ΓB A
            (M.compSub ΓPA ΓP ΓB (M.weakenSub ΓP A) σSnd)
            (M.varZero ΓP A)))
        (M.eqSub_trans ΓP ΓB left3 left4 σSnd
          (M.eqSub_symm ΓP ΓB left4 left3
            (M.compSub_assoc ΓP ΓPA ΓP ΓB τTop (M.weakenSub ΓP A) σSnd))
          (M.eqSub_trans ΓP ΓB left4 left5 σSnd
            (M.compSub_congr ΓP ΓP ΓB
              (M.compSub ΓP ΓPA ΓP τTop (M.weakenSub ΓP A)) (M.idSub ΓP)
              σSnd σSnd
              (M.extendSub_weaken ΓP ΓP A (M.idSub ΓP) fstP)
              (M.eqSub_refl ΓP ΓB σSnd))
            (M.compSub_id_left ΓP ΓB σSnd))))
  let hB : M.EqTm ΓP B (M.substTm ΓP ΓBA B compUnder weakB) sndP :=
    M.eq_trans ΓP B _ _ _
      (M.subst_congr ΓP ΓBA B compUnder compUnder weakB
        (M.substTm ΓBA ΓB B (M.weakenSub ΓB A) varB)
        (M.eqSub_refl ΓP ΓBA compUnder) (M.weakenTm_subst ΓB B A varB))
      (M.eq_trans ΓP B _ _ _
        (M.eq_symm ΓP B _ _
          (M.subst_comp ΓP ΓBA ΓB B compUnder (M.weakenSub ΓB A) varB))
        (M.eq_trans ΓP B _ _ _
          (M.subst_congr ΓP ΓB B
            (M.compSub ΓP ΓBA ΓB compUnder (M.weakenSub ΓB A)) σSnd
            varB varB hSubB (M.eq_refl ΓB B varB))
          (M.singletonSub_var sndP)))
  let hPair : M.EqTm ΓP (M.prodTy A B)
      (M.substTm ΓP ΓBA (M.prodTy A B) compUnder pairAB) prodVar :=
    M.eq_trans ΓP (M.prodTy A B) _ _ _
      (M.subst_pair ΓP ΓBA A B compUnder varA_BA weakB)
      (M.eq_trans ΓP (M.prodTy A B) _ _ _
        (M.pair_congr ΓP A B _ _ _ _ hA hB)
        (M.eq_symm ΓP (M.prodTy A B) _ _ (M.prod_eta ΓP A B prodVar)))
  let hAll : M.EqSub ΓP ΓP (M.compSub ΓP ΓBA ΓP compUnder σPair) (M.idSub ΓP) := by
    apply M.singletonSub_ext
    exact M.eq_trans ΓP (M.prodTy A B) _ _ _
      (M.subst_comp_singleton_var compUnder pairAB)
      (M.eq_trans ΓP (M.prodTy A B) _ _ _ hPair
        (M.eq_symm ΓP (M.prodTy A B) _ _ (M.subst_id ΓP (M.prodTy A B) prodVar)))
  let hlam : M.EqTm ΓP (M.arrowTy A C)
      (M.substTm ΓP ΓB (M.arrowTy A C) σSnd (M.curryTerm A B C f))
      (M.lam ΓP A C (M.substTm ΓPA ΓBA C σUnder body)) :=
    M.subst_lam ΓP ΓB A C σSnd body
  let happ : M.EqTm ΓP C
      (M.uncurryTerm A B C (M.curryTerm A B C f))
      (M.app ΓP A C (M.lam ΓP A C (M.substTm ΓPA ΓBA C σUnder body)) fstP) :=
    M.app_congr ΓP A C _ _ fstP fstP hlam (M.eq_refl ΓP A fstP)
  let hbeta : M.EqTm ΓP C
      (M.app ΓP A C (M.lam ΓP A C (M.substTm ΓPA ΓBA C σUnder body)) fstP)
      (M.substTop ΓP A C (M.substTm ΓPA ΓBA C σUnder body) fstP) :=
    M.beta ΓP A C (M.substTm ΓPA ΓBA C σUnder body) fstP
  let htop : M.EqTm ΓP C
      (M.substTop ΓP A C (M.substTm ΓPA ΓBA C σUnder body) fstP)
      (M.substTm ΓP ΓPA C τTop (M.substTm ΓPA ΓBA C σUnder body)) :=
    M.substTop_subst ΓP A C (M.substTm ΓPA ΓBA C σUnder body) fstP
  let hcollapse : M.EqTm ΓP C
      (M.substTm ΓP ΓPA C τTop (M.substTm ΓPA ΓBA C σUnder body)) f :=
    M.eq_trans ΓP C _ _ _
      (M.eq_symm ΓP C _ _ (M.subst_comp ΓP ΓPA ΓBA C τTop σUnder body))
      (M.eq_trans ΓP C _ _ _
        (M.eq_symm ΓP C _ _ (M.subst_comp ΓP ΓBA ΓP C compUnder σPair f))
        (M.eq_trans ΓP C _ _ _
          (M.subst_congr ΓP ΓP C (M.compSub ΓP ΓBA ΓP compUnder σPair) (M.idSub ΓP)
            f f hAll (M.eq_refl ΓP C f))
          (M.subst_id ΓP C f)))
  exact M.eq_trans ΓP C _ _ _ happ
    (M.eq_trans ΓP C _ _ _ hbeta
      (M.eq_trans ΓP C _ _ _ htop hcollapse))

/-- Quotient-level currying for one-variable morphisms in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.curryHom (M : LambdaCalculusModel)
    (A B C : M.Ty) : M.Hom (M.prodTy A B) C → M.Hom B (M.arrowTy A C) :=
  Quotient.lift
    (fun f => M.homMk (M.curryTerm A B C f))
    (by
      intro f g h
      let σ : M.Sub (M.extendCtx (M.singletonCtx B) A) (M.singletonCtx (M.prodTy A B)) :=
        M.singletonSub
          (M.pairTm (M.extendCtx (M.singletonCtx B) A) A B
            (M.varZero (M.singletonCtx B) A)
            (M.weakenTm (M.singletonCtx B) B A (M.varZero M.emptyCtx B)))
      exact M.homMk_eq (M.lam_congr (M.singletonCtx B) A C _ _
        (M.subst_congr (M.extendCtx (M.singletonCtx B) A) (M.singletonCtx (M.prodTy A B))
          C σ σ f g (M.eqSub_refl _ _ σ) h.some))
    )

/-- Quotient-level uncurrying for one-variable morphisms in the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.uncurryHom (M : LambdaCalculusModel)
    (A B C : M.Ty) : M.Hom B (M.arrowTy A C) → M.Hom (M.prodTy A B) C :=
  Quotient.lift
    (fun f => M.homMk (M.uncurryTerm A B C f))
    (by
      intro f g h
      let Γ := M.singletonCtx (M.prodTy A B)
      let σ : M.Sub Γ (M.singletonCtx B) :=
        M.singletonSub (M.sndTm Γ A B (M.varZero M.emptyCtx (M.prodTy A B)))
      let arg : M.Tm Γ A := M.fstTm Γ A B (M.varZero M.emptyCtx (M.prodTy A B))
      exact M.homMk_eq (M.app_congr Γ A C _ _ arg arg
        (M.subst_congr Γ (M.singletonCtx B) (M.arrowTy A C) σ σ f g
          (M.eqSub_refl _ _ σ) h.some)
        (M.eq_refl Γ A arg))
    )

/-- Quotient-level `uncurry (curry f) = f`. -/
theorem LambdaCalculus.LambdaCalculusModel.uncurry_curryHom (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Hom (M.prodTy A B) C) :
    M.uncurryHom A B C (M.curryHom A B C f) = f := by
  exact Quotient.inductionOn f fun f =>
    Quotient.sound ⟨M.uncurry_curryTerm A B C f⟩

/-- Quotient-level `curry (uncurry f) = f`. -/
theorem LambdaCalculus.LambdaCalculusModel.curry_uncurryHom (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Hom B (M.arrowTy A C)) :
    M.curryHom A B C (M.uncurryHom A B C f) = f := by
  exact Quotient.inductionOn f fun f =>
    Quotient.sound ⟨M.curry_uncurryTerm A B C f⟩

/-- The currying equivalence for the syntactic category. -/
def LambdaCalculus.LambdaCalculusModel.curryEquiv (M : LambdaCalculusModel)
    (A B C : M.Ty) : M.Hom (M.prodTy A B) C ≃ M.Hom B (M.arrowTy A C) where
  toFun := M.curryHom A B C
  invFun := M.uncurryHom A B C
  left_inv := M.uncurry_curryHom A B C
  right_inv := M.curry_uncurryHom A B C

/-- Postcomposition on function types, as a syntactic one-variable morphism. -/
def LambdaCalculus.LambdaCalculusModel.arrowMapTerm (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : M.Tm (M.singletonCtx B) C) :
    M.Tm (M.singletonCtx (M.arrowTy A B)) (M.arrowTy A C) :=
  M.curryTerm A (M.arrowTy A B) C
    (M.homComp (M.prodTy A (M.arrowTy A B)) B C
      (M.uncurryTerm A (M.arrowTy A B) B (M.varZero M.emptyCtx (M.arrowTy A B))) f)

/-- Naturality of uncurrying in the codomain, at the term level. -/
def LambdaCalculus.LambdaCalculusModel.uncurry_comp_arrowMapTerm (M : LambdaCalculusModel)
    (A B C D : M.Ty) (f : M.Tm (M.singletonCtx B) (M.arrowTy A C))
    (g : M.Tm (M.singletonCtx C) D) :
    M.EqTm (M.singletonCtx (M.prodTy A B)) D
      (M.uncurryTerm A B D
        (M.homComp B (M.arrowTy A C) (M.arrowTy A D) f (M.arrowMapTerm A C D g)))
      (M.homComp (M.prodTy A B) C D (M.uncurryTerm A B C f) g) := by
  let ΓP := M.singletonCtx (M.prodTy A B)
  let prodVar : M.Tm ΓP (M.prodTy A B) := M.varZero M.emptyCtx (M.prodTy A B)
  let fstP : M.Tm ΓP A := M.fstTm ΓP A B prodVar
  let sndP : M.Tm ΓP B := M.sndTm ΓP A B prodVar
  let σSnd : M.Sub ΓP (M.singletonCtx B) := M.singletonSub sndP
  let fnAtB : M.Tm ΓP (M.arrowTy A C) :=
    M.substTm ΓP (M.singletonCtx B) (M.arrowTy A C) σSnd f
  let pairAFn : M.Tm ΓP (M.prodTy A (M.arrowTy A C)) :=
    M.pairTm ΓP A (M.arrowTy A C) fstP fnAtB
  let σPairAFn : M.Sub ΓP (M.singletonCtx (M.prodTy A (M.arrowTy A C))) :=
    M.singletonSub pairAFn
  let ΓEval := M.singletonCtx (M.prodTy A (M.arrowTy A C))
  let varFn : M.Tm (M.singletonCtx (M.arrowTy A C)) (M.arrowTy A C) :=
    M.varZero M.emptyCtx (M.arrowTy A C)
  let evalC : M.Tm ΓEval C := M.uncurryTerm A (M.arrowTy A C) C varFn
  let evalThenG : M.Tm ΓEval D := M.homComp (M.prodTy A (M.arrowTy A C)) C D evalC g
  let arrowMap : M.Tm (M.singletonCtx (M.arrowTy A C)) (M.arrowTy A D) :=
    M.arrowMapTerm A C D g
  let hH : M.EqTm ΓP (M.arrowTy A D)
      (M.substTm ΓP (M.singletonCtx B) (M.arrowTy A D) σSnd
        (M.homComp B (M.arrowTy A C) (M.arrowTy A D) f arrowMap))
      (M.substTm ΓP (M.singletonCtx (M.arrowTy A C)) (M.arrowTy A D)
        (M.singletonSub fnAtB) arrowMap) :=
    M.subst_homComp B (M.arrowTy A C) (M.arrowTy A D) σSnd f arrowMap
  let hL₁ : M.EqTm ΓP D
      (M.uncurryTerm A B D
        (M.homComp B (M.arrowTy A C) (M.arrowTy A D) f arrowMap))
      (M.app ΓP A D
        (M.substTm ΓP (M.singletonCtx (M.arrowTy A C)) (M.arrowTy A D)
          (M.singletonSub fnAtB) arrowMap) fstP) :=
    M.app_congr ΓP A D _ _ fstP fstP hH (M.eq_refl ΓP A fstP)
  let hL₂ : M.EqTm ΓP D
      (M.app ΓP A D
        (M.substTm ΓP (M.singletonCtx (M.arrowTy A C)) (M.arrowTy A D)
          (M.singletonSub fnAtB) arrowMap) fstP)
      (M.substTm ΓP ΓEval D σPairAFn (M.uncurryTerm A (M.arrowTy A C) D arrowMap)) :=
    M.eq_symm ΓP D _ _ (M.subst_uncurryTerm_pair A (M.arrowTy A C) D fstP fnAtB arrowMap)
  let hL₃ : M.EqTm ΓP D
      (M.substTm ΓP ΓEval D σPairAFn (M.uncurryTerm A (M.arrowTy A C) D arrowMap))
      (M.substTm ΓP ΓEval D σPairAFn evalThenG) :=
    M.subst_congr ΓP ΓEval D σPairAFn σPairAFn _ _
      (M.eqSub_refl ΓP ΓEval σPairAFn)
      (M.uncurry_curryTerm A (M.arrowTy A C) D evalThenG)
  let hEval : M.EqTm ΓP C (M.substTm ΓP ΓEval C σPairAFn evalC)
      (M.uncurryTerm A B C f) :=
    M.eq_trans ΓP C _ _ _
      (M.subst_uncurryTerm_pair A (M.arrowTy A C) C fstP fnAtB varFn)
      (M.app_congr ΓP A C _ _ fstP fstP
        (M.singletonSub_var fnAtB) (M.eq_refl ΓP A fstP))
  let hR₁ : M.EqTm ΓP D
      (M.substTm ΓP ΓEval D σPairAFn evalThenG)
      (M.substTm ΓP (M.singletonCtx C) D
        (M.singletonSub (M.uncurryTerm A B C f)) g) :=
    M.eq_trans ΓP D _ _ _
      (M.subst_homComp (M.prodTy A (M.arrowTy A C)) C D σPairAFn evalC g)
      (M.subst_congr ΓP (M.singletonCtx C) D
        (M.singletonSub (M.substTm ΓP ΓEval C σPairAFn evalC))
        (M.singletonSub (M.uncurryTerm A B C f)) g g
        (M.singletonSub_congr hEval) (M.eq_refl (M.singletonCtx C) D g))
  let hR₂ : M.EqTm ΓP D
      (M.substTm ΓP (M.singletonCtx C) D
        (M.singletonSub (M.uncurryTerm A B C f)) g)
      (M.homComp (M.prodTy A B) C D (M.uncurryTerm A B C f) g) :=
    M.eq_symm ΓP D _ _ (M.homComp_subst (M.prodTy A B) C D (M.uncurryTerm A B C f) g)
  exact M.eq_trans ΓP D _ _ _ hL₁
    (M.eq_trans ΓP D _ _ _ hL₂
      (M.eq_trans ΓP D _ _ _ hL₃
        (M.eq_trans ΓP D _ _ _ hR₁ hR₂)))

/-- Naturality of uncurrying in the parameter, at the term level. -/
def LambdaCalculus.LambdaCalculusModel.uncurry_comp_curryTerm (M : LambdaCalculusModel)
    (A B B' C : M.Ty) (f : M.Tm (M.singletonCtx B') B)
    (g : M.Tm (M.singletonCtx (M.prodTy A B)) C) :
    M.EqTm (M.singletonCtx (M.prodTy A B')) C
      (M.uncurryTerm A B' C
        (M.homComp B' B (M.arrowTy A C) f (M.curryTerm A B C g)))
      (M.homComp (M.prodTy A B') (M.prodTy A B) C
        (M.pairTm (M.singletonCtx (M.prodTy A B')) A B
          (M.homComp (M.prodTy A B') A A
            (M.fstTm (M.singletonCtx (M.prodTy A B')) A B'
              (M.varZero M.emptyCtx (M.prodTy A B')))
            (M.varZero M.emptyCtx A))
          (M.homComp (M.prodTy A B') B' B
            (M.sndTm (M.singletonCtx (M.prodTy A B')) A B'
              (M.varZero M.emptyCtx (M.prodTy A B'))) f))
        g) := by
  let ΓP' := M.singletonCtx (M.prodTy A B')
  let prodVar' : M.Tm ΓP' (M.prodTy A B') := M.varZero M.emptyCtx (M.prodTy A B')
  let fstP' : M.Tm ΓP' A := M.fstTm ΓP' A B' prodVar'
  let sndP' : M.Tm ΓP' B' := M.sndTm ΓP' A B' prodVar'
  let σSnd' : M.Sub ΓP' (M.singletonCtx B') := M.singletonSub sndP'
  let fAtB' : M.Tm ΓP' B := M.substTm ΓP' (M.singletonCtx B') B σSnd' f
  let fComp : M.Tm ΓP' B := M.homComp (M.prodTy A B') B' B sndP' f
  let pairSimple : M.Tm ΓP' (M.prodTy A B) := M.pairTm ΓP' A B fstP' fAtB'
  let pairTensor : M.Tm ΓP' (M.prodTy A B) :=
    M.pairTm ΓP' A B
      (M.homComp (M.prodTy A B') A A fstP' (M.varZero M.emptyCtx A)) fComp
  let σPairSimple : M.Sub ΓP' (M.singletonCtx (M.prodTy A B)) := M.singletonSub pairSimple
  let hH : M.EqTm ΓP' (M.arrowTy A C)
      (M.substTm ΓP' (M.singletonCtx B') (M.arrowTy A C) σSnd'
        (M.homComp B' B (M.arrowTy A C) f (M.curryTerm A B C g)))
      (M.substTm ΓP' (M.singletonCtx B) (M.arrowTy A C)
        (M.singletonSub fAtB') (M.curryTerm A B C g)) :=
    M.subst_homComp B' B (M.arrowTy A C) σSnd' f (M.curryTerm A B C g)
  let hL₁ : M.EqTm ΓP' C
      (M.uncurryTerm A B' C
        (M.homComp B' B (M.arrowTy A C) f (M.curryTerm A B C g)))
      (M.app ΓP' A C
        (M.substTm ΓP' (M.singletonCtx B) (M.arrowTy A C)
          (M.singletonSub fAtB') (M.curryTerm A B C g)) fstP') :=
    M.app_congr ΓP' A C _ _ fstP' fstP' hH (M.eq_refl ΓP' A fstP')
  let hL₂ : M.EqTm ΓP' C
      (M.app ΓP' A C
        (M.substTm ΓP' (M.singletonCtx B) (M.arrowTy A C)
          (M.singletonSub fAtB') (M.curryTerm A B C g)) fstP')
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple
        (M.uncurryTerm A B C (M.curryTerm A B C g))) :=
    M.eq_symm ΓP' C _ _ (M.subst_uncurryTerm_pair A B C fstP' fAtB' (M.curryTerm A B C g))
  let hL₃ : M.EqTm ΓP' C
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple
        (M.uncurryTerm A B C (M.curryTerm A B C g)))
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple g) :=
    M.subst_congr ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple σPairSimple _ _
      (M.eqSub_refl ΓP' (M.singletonCtx (M.prodTy A B)) σPairSimple)
      (M.uncurry_curryTerm A B C g)
  let hPair : M.EqTm ΓP' (M.prodTy A B) pairSimple pairTensor :=
    M.pair_congr ΓP' A B _ _ _ _
      (M.eq_symm ΓP' A _ _ (M.homComp_id_right (M.prodTy A B') A fstP'))
      (M.eq_symm ΓP' B _ _ (M.homComp_subst (M.prodTy A B') B' B sndP' f))
  let hL₄ : M.EqTm ΓP' C
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple g)
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C (M.singletonSub pairTensor) g) :=
    M.subst_congr ΓP' (M.singletonCtx (M.prodTy A B)) C σPairSimple (M.singletonSub pairTensor) g g
      (M.singletonSub_congr hPair) (M.eq_refl (M.singletonCtx (M.prodTy A B)) C g)
  let hR : M.EqTm ΓP' C
      (M.substTm ΓP' (M.singletonCtx (M.prodTy A B)) C (M.singletonSub pairTensor) g)
      (M.homComp (M.prodTy A B') (M.prodTy A B) C pairTensor g) :=
    M.eq_symm ΓP' C _ _ (M.homComp_subst (M.prodTy A B') (M.prodTy A B) C pairTensor g)
  exact M.eq_trans ΓP' C _ _ _ hL₁
    (M.eq_trans ΓP' C _ _ _ hL₂
      (M.eq_trans ΓP' C _ _ _ hL₃
        (M.eq_trans ΓP' C _ _ _ hL₄ hR)))

/-- Postcomposition on function types descends to quotient morphisms. -/
def LambdaCalculus.LambdaCalculusModel.arrowMapHom (M : LambdaCalculusModel)
    (A B C : M.Ty) : M.Hom B C → M.Hom (M.arrowTy A B) (M.arrowTy A C) :=
  Quotient.lift
    (fun f => M.homMk (M.arrowMapTerm A B C f))
    (by
      intro f g h
      have hcomp :
          M.homMk (M.homComp (M.prodTy A (M.arrowTy A B)) B C
            (M.uncurryTerm A (M.arrowTy A B) B (M.varZero M.emptyCtx (M.arrowTy A B))) f) =
          M.homMk (M.homComp (M.prodTy A (M.arrowTy A B)) B C
            (M.uncurryTerm A (M.arrowTy A B) B (M.varZero M.emptyCtx (M.arrowTy A B))) g) :=
        Quotient.sound ⟨M.homComp_congr (M.prodTy A (M.arrowTy A B)) B C _ _ f g
          (M.eq_refl _ _ _) h.some⟩
      exact congrArg (M.curryHom A (M.arrowTy A B) C) hcomp)

/-- Uncurrying postcomposition on function types gives postcomposition after evaluation. -/
theorem LambdaCalculus.LambdaCalculusModel.uncurry_arrowMapHom (M : LambdaCalculusModel)
    (A B C : M.Ty) (f : B ⟶ C) :
    M.uncurryHom A (M.arrowTy A B) C (M.arrowMapHom A B C f) =
      M.uncurryHom A (M.arrowTy A B) B (𝟙 (M.arrowTy A B)) ≫ f := by
  exact Quotient.inductionOn (f : M.Hom B C) fun f => by
    change M.uncurryHom A (M.arrowTy A B) C
        (M.curryHom A (M.arrowTy A B) C
          (M.homMk (M.homComp (M.prodTy A (M.arrowTy A B)) B C
            (M.uncurryTerm A (M.arrowTy A B) B (M.varZero M.emptyCtx (M.arrowTy A B))) f))) = _
    rw [M.uncurry_curryHom]
    rfl

/-- Naturality of uncurrying in the codomain. -/
theorem LambdaCalculus.LambdaCalculusModel.uncurry_comp_arrowMapHom (M : LambdaCalculusModel)
    (A B C D : M.Ty) (f : B ⟶ M.arrowTy A C) (g : C ⟶ D) :
    M.uncurryHom A B D (f ≫ M.arrowMapHom A C D g) =
      M.uncurryHom A B C f ≫ g := by
  exact Quotient.inductionOn (f : M.Hom B (M.arrowTy A C)) fun fterm => by
    exact Quotient.inductionOn (g : M.Hom C D) fun gterm => by
      exact Quotient.sound ⟨M.uncurry_comp_arrowMapTerm A B C D fterm gterm⟩

/-- The chosen cartesian tensor map is represented by pairing first projection with postcomposition
of the second projection. -/
theorem LambdaCalculus.LambdaCalculusModel.tensorLeft_map_homMk (M : LambdaCalculusModel)
    (A B B' : M.Ty) (f : M.Tm (M.singletonCtx B') B) :
    ((tensorLeft A).map (M.homMk f : B' ⟶ B) : (A ⊗ B') ⟶ (A ⊗ B)) =
      M.homMk (M.pairTm (M.singletonCtx (M.prodTy A B')) A B
        (M.homComp (M.prodTy A B') A A
          (M.fstTm (M.singletonCtx (M.prodTy A B')) A B'
            (M.varZero M.emptyCtx (M.prodTy A B')))
          (M.varZero M.emptyCtx A))
        (M.homComp (M.prodTy A B') B' B
          (M.sndTm (M.singletonCtx (M.prodTy A B')) A B'
            (M.varZero M.emptyCtx (M.prodTy A B'))) f)) := rfl

/-- Naturality of uncurrying in the parameter. -/
theorem LambdaCalculus.LambdaCalculusModel.uncurry_comp_curryHom (M : LambdaCalculusModel)
    (A B B' C : M.Ty) (f : B' ⟶ B) (g : (A ⊗ B) ⟶ C) :
    M.uncurryHom A B' C (f ≫ M.curryHom A B C g) =
      (tensorLeft A).map f ≫ g := by
  exact Quotient.inductionOn (f : M.Hom B' B) fun fterm => by
    exact Quotient.inductionOn (g : M.Hom (M.prodTy A B) C) fun gterm => by
      rw [M.tensorLeft_map_homMk A B B' fterm]
      exact Quotient.sound ⟨M.uncurry_comp_curryTerm A B B' C fterm gterm⟩

/-- The internal-hom functor represented by a fixed syntactic type. -/
def LambdaCalculus.LambdaCalculusModel.ihomFunctor (M : LambdaCalculusModel)
    (A : M.Ty) : M.category ⥤ M.category where
  obj B := M.arrowTy A B
  map {B C} f := M.arrowMapHom A B C f
  map_id B := by
    apply (M.curryEquiv A (M.arrowTy A B) B).symm.injective
    change M.uncurryHom A (M.arrowTy A B) B (M.arrowMapHom A B B (𝟙 B)) =
      M.uncurryHom A (M.arrowTy A B) B (𝟙 (M.arrowTy A B))
    rw [M.uncurry_arrowMapHom]
    simp
  map_comp {B C D} f g := by
    apply (M.curryEquiv A (M.arrowTy A B) D).symm.injective
    change M.uncurryHom A (M.arrowTy A B) D (M.arrowMapHom A B D (f ≫ g : B ⟶ D)) =
      M.uncurryHom A (M.arrowTy A B) D
        (((M.arrowMapHom A B C f : (M.arrowTy A B) ⟶ (M.arrowTy A C)) ≫
          (M.arrowMapHom A C D g : (M.arrowTy A C) ⟶ (M.arrowTy A D)) :
          (M.arrowTy A B) ⟶ (M.arrowTy A D)))
    rw [M.uncurry_arrowMapHom, M.uncurry_comp_arrowMapHom, M.uncurry_arrowMapHom]
    simp [Category.assoc]

/-- Naturality of currying in the codomain. -/
theorem LambdaCalculus.LambdaCalculusModel.curry_natural_right_hom (M : LambdaCalculusModel)
    (A B C D : M.Ty) (f : (A ⊗ B) ⟶ C) (g : C ⟶ D) :
    M.curryHom A B D (f ≫ g) = M.curryHom A B C f ≫ (M.ihomFunctor A).map g := by
  apply (M.curryEquiv A B D).symm.injective
  change M.uncurryHom A B D (M.curryHom A B D (f ≫ g : (A ⊗ B) ⟶ D)) =
    M.uncurryHom A B D
      (((M.curryHom A B C f : B ⟶ M.arrowTy A C) ≫
        (M.arrowMapHom A C D g : M.arrowTy A C ⟶ M.arrowTy A D) :
        B ⟶ M.arrowTy A D))
  rw [M.uncurry_curryHom, M.uncurry_comp_arrowMapHom, M.uncurry_curryHom]
  rfl

/-- Naturality of currying in the parameter. -/
theorem LambdaCalculus.LambdaCalculusModel.curry_natural_left_hom (M : LambdaCalculusModel)
    (A B B' C : M.Ty) (f : B' ⟶ B) (g : (A ⊗ B) ⟶ C) :
    M.curryHom A B' C ((tensorLeft A).map f ≫ g) = f ≫ M.curryHom A B C g := by
  apply (M.curryEquiv A B' C).symm.injective
  change M.uncurryHom A B' C (M.curryHom A B' C ((tensorLeft A).map f ≫ g)) =
    M.uncurryHom A B' C (f ≫ M.curryHom A B C g)
  rw [M.uncurry_curryHom, M.uncurry_comp_curryHom]

/-- Each syntactic type is closed in the syntactic cartesian monoidal category. -/
@[reducible]
def LambdaCalculus.LambdaCalculusModel.closed (M : LambdaCalculusModel) (A : M.Ty) : Closed A where
  rightAdj := M.ihomFunctor A
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun B C => M.curryEquiv A B C
      homEquiv_naturality_left_symm := by
        intro B' B C f g
        apply (M.curryEquiv A B' C).injective
        change M.curryHom A B' C (M.uncurryHom A B' C (f ≫ g)) =
          M.curryHom A B' C ((tensorLeft A).map f ≫ M.uncurryHom A B C g)
        rw [M.curry_uncurryHom, M.curry_natural_left_hom, M.curry_uncurryHom]
      homEquiv_naturality_right := by
        intro B C D f g
        exact M.curry_natural_right_hom A B C D f g }

instance : MonoidalClosed M.category where
  closed := M.closed

end CurryHowardLambekBackward

section Equivalence

variable (C : Type) [Category C] [CartesianMonoidalCategory C] [MonoidalClosed C]

namespace CCC

/-- The canonical functor from a CCC to the syntactic category of its interpreted STLC model. -/
def toSyntacticFunctor : C ⥤ (CCC.lambdaCalculusModel C).category where
  obj X := X
  map {X Y} f :=
    (CCC.lambdaCalculusModel C).homMk («snd» (𝟙_ C) X ≫ f)
  map_id X := by
    show (CCC.lambdaCalculusModel C).homMk («snd» (𝟙_ C) X ≫ 𝟙 X) =
      (CCC.lambdaCalculusModel C).homMk («snd» (𝟙_ C) X)
    exact Quotient.sound ⟨⟨by simp⟩⟩
  map_comp {X Y Z} f g := by
    let M := CCC.lambdaCalculusModel C
    show M.homMk («snd» (𝟙_ C) X ≫ (f ≫ g)) =
      M.homMk (M.homComp X Y Z («snd» (𝟙_ C) X ≫ f) («snd» (𝟙_ C) Y ≫ g))
    exact Quotient.sound ⟨⟨by
      change «snd» (𝟙_ C) X ≫ (f ≫ g) =
        lift (toUnit (𝟙_ C ⊗ X)) («snd» (𝟙_ C) X ≫ f) ≫ («snd» (𝟙_ C) Y ≫ g)
      calc
        «snd» (𝟙_ C) X ≫ (f ≫ g) = («snd» (𝟙_ C) X ≫ f) ≫ g := by
          rw [Category.assoc]
        _ = (lift (toUnit (𝟙_ C ⊗ X)) («snd» (𝟙_ C) X ≫ f) ≫ «snd» (𝟙_ C) Y) ≫ g := by
          simp
        _ = lift (toUnit (𝟙_ C ⊗ X)) («snd» (𝟙_ C) X ≫ f) ≫ («snd» (𝟙_ C) Y ≫ g) := by
          rw [Category.assoc]
    ⟩⟩

instance : (toSyntacticFunctor C).Faithful where
  map_injective := by
    intro X Y f g h
    let M := CCC.lambdaCalculusModel C
    change M.homMk («snd» (𝟙_ C) X ≫ f) = M.homMk («snd» (𝟙_ C) X ≫ g) at h
    rw [Quotient.eq] at h
    rcases h with ⟨hEq⟩
    have hmap : «snd» (𝟙_ C) X ≫ f = «snd» (𝟙_ C) X ≫ g := hEq.down
    have hpre := congrArg (fun k => (λ_ X).inv ≫ k) hmap
    simpa [← leftUnitor_hom X, Category.assoc] using hpre

instance : (toSyntacticFunctor C).Full where
  map_surjective := by
    intro X Y h
    let M := CCC.lambdaCalculusModel C
    exact Quotient.inductionOn h (fun t => by
      use ((λ_ X).inv ≫ t)
      change M.homMk («snd» (𝟙_ C) X ≫ ((λ_ X).inv ≫ t)) = M.homMk t
      exact Quotient.sound ⟨⟨by
        change «snd» (𝟙_ C) X ≫ ((λ_ X).inv ≫ (t : 𝟙_ C ⊗ X ⟶ Y)) = t
        rw [← leftUnitor_hom X]
        simp
      ⟩⟩)

instance : (toSyntacticFunctor C).EssSurj where
  mem_essImage Y := ⟨Y, ⟨Iso.refl Y⟩⟩

instance : (toSyntacticFunctor C).IsEquivalence where

end CCC

/-- The Curry-Howard-Lambek comparison equivalence from a CCC to its syntactic category. -/
noncomputable def equivalence : C ≌ (CCC.lambdaCalculusModel C).category :=
  Functor.asEquivalence (CCC.toSyntacticFunctor C)

noncomputable instance : (equivalence C).functor.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts (equivalence C).functor

noncomputable instance : (equivalence C).inverse.Monoidal :=
  (equivalence C).inverseMonoidal

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (equivalence C).IsMonoidal :=
  letI := (equivalence C).inverseMonoidal
  inferInstance

end Equivalence

section CurryHowardLambekTwoSidedStatement

namespace LambdaCalculus

/-- Definitional equality quotient for terms in an arbitrary context. -/
def LambdaCalculusModel.termSetoid (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) : Setoid (M.Tm Γ A) where
  r t u := Nonempty (M.EqTm Γ A t u)
  iseqv :=
    { refl := fun t => ⟨M.eq_refl Γ A t⟩
      symm := fun h => ⟨M.eq_symm Γ A _ _ h.some⟩
      trans := fun h₁ h₂ => ⟨M.eq_trans Γ A _ _ _ h₁.some h₂.some⟩ }

/-- Terms in an arbitrary context modulo definitional equality. -/
abbrev LambdaCalculusModel.TermQuot (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) : Type :=
  Quotient (M.termSetoid Γ A)

/-- Quotient constructor for terms in arbitrary context. -/
abbrev LambdaCalculusModel.termMk (M : LambdaCalculusModel) {Γ : M.Ctx} {A : M.Ty}
    (t : M.Tm Γ A) : M.TermQuot Γ A :=
  Quotient.mk (M.termSetoid Γ A) t

/-- Definitional equality quotient for explicit substitutions. -/
def LambdaCalculusModel.subSetoid (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) : Setoid (M.Sub Γ Δ) where
  r σ τ := Nonempty (M.EqSub Γ Δ σ τ)
  iseqv :=
    { refl := fun σ => ⟨M.eqSub_refl Γ Δ σ⟩
      symm := fun h => ⟨M.eqSub_symm Γ Δ _ _ h.some⟩
      trans := fun h₁ h₂ => ⟨M.eqSub_trans Γ Δ _ _ _ h₁.some h₂.some⟩ }

/-- Substitutions modulo definitional equality. -/
abbrev LambdaCalculusModel.SubQuot (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) : Type :=
  Quotient (M.subSetoid Γ Δ)

/-- Quotient constructor for substitutions. -/
abbrev LambdaCalculusModel.subMk (M : LambdaCalculusModel) {Γ Δ : M.Ctx}
    (σ : M.Sub Γ Δ) : M.SubQuot Γ Δ :=
  Quotient.mk (M.subSetoid Γ Δ) σ

/-- The singleton context representing an arbitrary context. -/
abbrev LambdaCalculusModel.repCtx (M : LambdaCalculusModel) (Γ : M.Ctx) : M.Ctx :=
  M.singletonCtx (M.ctxObj Γ)

/-- Encode a term in an arbitrary context as a one-variable term. -/
def LambdaCalculusModel.contextTermEncode (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (t : M.Tm Γ A) : M.Tm (M.repCtx Γ) A :=
  M.substTm (M.repCtx Γ) Γ A (M.ctxFromSingleton Γ) t

/-- Decode a one-variable term at the representing object as a term in the represented context. -/
def LambdaCalculusModel.contextTermDecode (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (t : M.Tm (M.repCtx Γ) A) : M.Tm Γ A :=
  M.substTm Γ (M.repCtx Γ) A (M.ctxToSingleton Γ) t

/-- Decoding after encoding is definitionally equal to the original term. -/
def LambdaCalculusModel.contextTermDecode_encode (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (t : M.Tm Γ A) :
    M.EqTm Γ A (M.contextTermDecode Γ A (M.contextTermEncode Γ A t)) t :=
  M.eq_trans Γ A _ _ _
    (M.eq_symm Γ A _ _
      (M.subst_comp Γ (M.repCtx Γ) Γ A (M.ctxToSingleton Γ) (M.ctxFromSingleton Γ) t))
    (M.eq_trans Γ A _ _ _
      (M.subst_congr Γ Γ A
        (M.compSub Γ (M.repCtx Γ) Γ (M.ctxToSingleton Γ) (M.ctxFromSingleton Γ))
        (M.idSub Γ) t t (M.ctxToFrom Γ) (M.eq_refl Γ A t))
      (M.subst_id Γ A t))

/-- Encoding after decoding is definitionally equal to the original one-variable term. -/
def LambdaCalculusModel.contextTermEncode_decode (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) (t : M.Tm (M.repCtx Γ) A) :
    M.EqTm (M.repCtx Γ) A (M.contextTermEncode Γ A (M.contextTermDecode Γ A t)) t :=
  M.eq_trans (M.repCtx Γ) A _ _ _
    (M.eq_symm (M.repCtx Γ) A _ _
      (M.subst_comp (M.repCtx Γ) Γ (M.repCtx Γ) A (M.ctxFromSingleton Γ)
        (M.ctxToSingleton Γ) t))
    (M.eq_trans (M.repCtx Γ) A _ _ _
      (M.subst_congr (M.repCtx Γ) (M.repCtx Γ) A
        (M.compSub (M.repCtx Γ) Γ (M.repCtx Γ) (M.ctxFromSingleton Γ)
          (M.ctxToSingleton Γ))
        (M.idSub (M.repCtx Γ)) t t (M.ctxFromTo Γ) (M.eq_refl (M.repCtx Γ) A t))
      (M.subst_id (M.repCtx Γ) A t))

/-- The quotient-level term comparison equivalence supplied by context representability. -/
def LambdaCalculusModel.contextTermEquiv (M : LambdaCalculusModel)
    (Γ : M.Ctx) (A : M.Ty) : M.TermQuot Γ A ≃ M.Hom (M.ctxObj Γ) A where
  toFun := Quotient.lift
    (fun t => M.homMk (M.contextTermEncode Γ A t))
    (by
      intro t u h
      exact M.homMk_eq (M.subst_congr (M.repCtx Γ) Γ A
        (M.ctxFromSingleton Γ) (M.ctxFromSingleton Γ) t u
        (M.eqSub_refl (M.repCtx Γ) Γ (M.ctxFromSingleton Γ)) h.some))
  invFun := Quotient.lift
    (fun t => M.termMk (M.contextTermDecode Γ A t))
    (by
      intro t u h
      exact Quotient.sound ⟨M.subst_congr Γ (M.repCtx Γ) A
        (M.ctxToSingleton Γ) (M.ctxToSingleton Γ) t u
        (M.eqSub_refl Γ (M.repCtx Γ) (M.ctxToSingleton Γ)) h.some⟩)
  left_inv := by
    intro x
    exact Quotient.inductionOn x fun t =>
      Quotient.sound ⟨M.contextTermDecode_encode Γ A t⟩
  right_inv := by
    intro x
    exact Quotient.inductionOn x fun t =>
      Quotient.sound ⟨M.contextTermEncode_decode Γ A t⟩

/-- The code term of a represented context. -/
def LambdaCalculusModel.ctxCode (M : LambdaCalculusModel) (Γ : M.Ctx) :
    M.Tm Γ (M.ctxObj Γ) :=
  M.substTm Γ (M.repCtx Γ) (M.ctxObj Γ) (M.ctxToSingleton Γ)
    (M.varZero M.emptyCtx (M.ctxObj Γ))

/-- Encode a substitution as a term of the represented codomain context object. -/
def LambdaCalculusModel.contextSubToTerm (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) (σ : M.Sub Γ Δ) : M.Tm Γ (M.ctxObj Δ) :=
  M.substTm Γ (M.repCtx Δ) (M.ctxObj Δ)
    (M.compSub Γ Δ (M.repCtx Δ) σ (M.ctxToSingleton Δ))
    (M.varZero M.emptyCtx (M.ctxObj Δ))

/-- Decode a term of a represented context object as a substitution into that context. -/
def LambdaCalculusModel.contextTermToSub (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) (t : M.Tm Γ (M.ctxObj Δ)) : M.Sub Γ Δ :=
  M.compSub Γ (M.repCtx Δ) Δ (M.singletonSub t) (M.ctxFromSingleton Δ)

/-- The substitution code agrees with substituting the codomain code term. -/
def LambdaCalculusModel.contextSubToTerm_eq_subst_code (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) (σ : M.Sub Γ Δ) :
    M.EqTm Γ (M.ctxObj Δ) (M.contextSubToTerm Γ Δ σ)
      (M.substTm Γ Δ (M.ctxObj Δ) σ (M.ctxCode Δ)) :=
  M.subst_comp Γ Δ (M.repCtx Δ) (M.ctxObj Δ) σ (M.ctxToSingleton Δ)
    (M.varZero M.emptyCtx (M.ctxObj Δ))

/-- The singleton substitution classified by the context code is the representing substitution. -/
def LambdaCalculusModel.singletonSub_ctxCode (M : LambdaCalculusModel) (Δ : M.Ctx) :
    M.EqSub Δ (M.repCtx Δ) (M.singletonSub (M.ctxCode Δ)) (M.ctxToSingleton Δ) :=
  M.eqSub_symm Δ (M.repCtx Δ) (M.ctxToSingleton Δ) (M.singletonSub (M.ctxCode Δ))
    (M.singletonSub_eta (M.ctxToSingleton Δ))

/-- Decoding after encoding is definitionally equal to the original substitution. -/
def LambdaCalculusModel.contextTermToSub_subToTerm (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) (σ : M.Sub Γ Δ) :
    M.EqSub Γ Δ (M.contextTermToSub Γ Δ (M.contextSubToTerm Γ Δ σ)) σ := by
  let SΔ := M.repCtx Δ
  let code : M.Tm Δ (M.ctxObj Δ) := M.ctxCode Δ
  let left0 : M.Sub Γ Δ := M.contextTermToSub Γ Δ (M.contextSubToTerm Γ Δ σ)
  let left1 : M.Sub Γ Δ := M.compSub Γ SΔ Δ
    (M.singletonSub (M.substTm Γ Δ (M.ctxObj Δ) σ code)) (M.ctxFromSingleton Δ)
  let left2 : M.Sub Γ Δ := M.compSub Γ SΔ Δ
    (M.compSub Γ Δ SΔ σ (M.singletonSub code)) (M.ctxFromSingleton Δ)
  let left3 : M.Sub Γ Δ := M.compSub Γ Δ Δ σ
    (M.compSub Δ SΔ Δ (M.singletonSub code) (M.ctxFromSingleton Δ))
  let left4 : M.Sub Γ Δ := M.compSub Γ Δ Δ σ
    (M.compSub Δ SΔ Δ (M.ctxToSingleton Δ) (M.ctxFromSingleton Δ))
  let left5 : M.Sub Γ Δ := M.compSub Γ Δ Δ σ (M.idSub Δ)
  exact M.eqSub_trans Γ Δ left0 left1 σ
    (M.compSub_congr Γ SΔ Δ
      (M.singletonSub (M.contextSubToTerm Γ Δ σ))
      (M.singletonSub (M.substTm Γ Δ (M.ctxObj Δ) σ code))
      (M.ctxFromSingleton Δ) (M.ctxFromSingleton Δ)
      (M.singletonSub_congr (M.contextSubToTerm_eq_subst_code Γ Δ σ))
      (M.eqSub_refl SΔ Δ (M.ctxFromSingleton Δ)))
    (M.eqSub_trans Γ Δ left1 left2 σ
      (M.compSub_congr Γ SΔ Δ
        (M.singletonSub (M.substTm Γ Δ (M.ctxObj Δ) σ code))
        (M.compSub Γ Δ SΔ σ (M.singletonSub code))
        (M.ctxFromSingleton Δ) (M.ctxFromSingleton Δ)
        (M.eqSub_symm Γ SΔ (M.compSub Γ Δ SΔ σ (M.singletonSub code))
          (M.singletonSub (M.substTm Γ Δ (M.ctxObj Δ) σ code))
          (M.singletonSub_comp σ code))
        (M.eqSub_refl SΔ Δ (M.ctxFromSingleton Δ)))
      (M.eqSub_trans Γ Δ left2 left3 σ
        (M.compSub_assoc Γ Δ SΔ Δ σ (M.singletonSub code) (M.ctxFromSingleton Δ))
        (M.eqSub_trans Γ Δ left3 left4 σ
          (M.compSub_congr Γ Δ Δ σ σ
            (M.compSub Δ SΔ Δ (M.singletonSub code) (M.ctxFromSingleton Δ))
            (M.compSub Δ SΔ Δ (M.ctxToSingleton Δ) (M.ctxFromSingleton Δ))
            (M.eqSub_refl Γ Δ σ)
            (M.compSub_congr Δ SΔ Δ (M.singletonSub code) (M.ctxToSingleton Δ)
              (M.ctxFromSingleton Δ) (M.ctxFromSingleton Δ)
              (M.singletonSub_ctxCode Δ)
              (M.eqSub_refl SΔ Δ (M.ctxFromSingleton Δ))))
          (M.eqSub_trans Γ Δ left4 left5 σ
            (M.compSub_congr Γ Δ Δ σ σ
              (M.compSub Δ SΔ Δ (M.ctxToSingleton Δ) (M.ctxFromSingleton Δ))
              (M.idSub Δ)
              (M.eqSub_refl Γ Δ σ) (M.ctxToFrom Δ))
            (M.compSub_id_right Γ Δ σ)))))

/-- Encoding after decoding is definitionally equal to the original context-code term. -/
def LambdaCalculusModel.contextSubToTerm_termToSub (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) (t : M.Tm Γ (M.ctxObj Δ)) :
    M.EqTm Γ (M.ctxObj Δ) (M.contextSubToTerm Γ Δ (M.contextTermToSub Γ Δ t)) t := by
  let SΔ := M.repCtx Δ
  let leftSub0 : M.Sub Γ SΔ :=
    M.compSub Γ Δ SΔ (M.contextTermToSub Γ Δ t) (M.ctxToSingleton Δ)
  let leftSub1 : M.Sub Γ SΔ :=
    M.compSub Γ Δ SΔ
      (M.compSub Γ SΔ Δ (M.singletonSub t) (M.ctxFromSingleton Δ))
      (M.ctxToSingleton Δ)
  let leftSub2 : M.Sub Γ SΔ :=
    M.compSub Γ SΔ SΔ (M.singletonSub t)
      (M.compSub SΔ Δ SΔ (M.ctxFromSingleton Δ) (M.ctxToSingleton Δ))
  let leftSub3 : M.Sub Γ SΔ :=
    M.compSub Γ SΔ SΔ (M.singletonSub t) (M.idSub SΔ)
  let hsub : M.EqSub Γ SΔ leftSub0 (M.singletonSub t) :=
    M.eqSub_trans Γ SΔ leftSub0 leftSub1 (M.singletonSub t)
      (M.eqSub_refl Γ SΔ leftSub0)
      (M.eqSub_trans Γ SΔ leftSub1 leftSub2 (M.singletonSub t)
        (M.compSub_assoc Γ SΔ Δ SΔ (M.singletonSub t) (M.ctxFromSingleton Δ)
          (M.ctxToSingleton Δ))
        (M.eqSub_trans Γ SΔ leftSub2 leftSub3 (M.singletonSub t)
          (M.compSub_congr Γ SΔ SΔ (M.singletonSub t) (M.singletonSub t)
            (M.compSub SΔ Δ SΔ (M.ctxFromSingleton Δ) (M.ctxToSingleton Δ))
            (M.idSub SΔ)
            (M.eqSub_refl Γ SΔ (M.singletonSub t)) (M.ctxFromTo Δ))
          (M.compSub_id_right Γ SΔ (M.singletonSub t))))
  exact M.eq_trans Γ (M.ctxObj Δ) _ _ _
    (M.subst_congr Γ SΔ (M.ctxObj Δ) leftSub0 (M.singletonSub t)
      (M.varZero M.emptyCtx (M.ctxObj Δ)) (M.varZero M.emptyCtx (M.ctxObj Δ))
      hsub (M.eq_refl SΔ (M.ctxObj Δ) (M.varZero M.emptyCtx (M.ctxObj Δ))))
    (M.singletonSub_var t)

/-- The quotient-level substitution comparison equivalence supplied by context representability. -/
def LambdaCalculusModel.contextSubEquiv (M : LambdaCalculusModel)
    (Γ Δ : M.Ctx) : M.SubQuot Γ Δ ≃ M.Hom (M.ctxObj Γ) (M.ctxObj Δ) where
  toFun := Quotient.lift
    (fun σ => M.homMk (M.contextTermEncode Γ (M.ctxObj Δ) (M.contextSubToTerm Γ Δ σ)))
    (by
      intro σ τ h
      exact M.homMk_eq (M.subst_congr (M.repCtx Γ) Γ (M.ctxObj Δ)
        (M.ctxFromSingleton Γ) (M.ctxFromSingleton Γ)
        (M.contextSubToTerm Γ Δ σ) (M.contextSubToTerm Γ Δ τ)
        (M.eqSub_refl (M.repCtx Γ) Γ (M.ctxFromSingleton Γ))
        (M.subst_congr Γ (M.repCtx Δ) (M.ctxObj Δ)
          (M.compSub Γ Δ (M.repCtx Δ) σ (M.ctxToSingleton Δ))
          (M.compSub Γ Δ (M.repCtx Δ) τ (M.ctxToSingleton Δ))
          (M.varZero M.emptyCtx (M.ctxObj Δ)) (M.varZero M.emptyCtx (M.ctxObj Δ))
          (M.compSub_congr Γ Δ (M.repCtx Δ) σ τ (M.ctxToSingleton Δ)
            (M.ctxToSingleton Δ) h.some
            (M.eqSub_refl Δ (M.repCtx Δ) (M.ctxToSingleton Δ)))
          (M.eq_refl (M.repCtx Δ) (M.ctxObj Δ)
            (M.varZero M.emptyCtx (M.ctxObj Δ))))))
  invFun := Quotient.lift
    (fun f => M.subMk (M.contextTermToSub Γ Δ
      (M.contextTermDecode Γ (M.ctxObj Δ) f)))
    (by
      intro f g h
      exact Quotient.sound ⟨M.compSub_congr Γ (M.repCtx Δ) Δ
        (M.singletonSub (M.contextTermDecode Γ (M.ctxObj Δ) f))
        (M.singletonSub (M.contextTermDecode Γ (M.ctxObj Δ) g))
        (M.ctxFromSingleton Δ) (M.ctxFromSingleton Δ)
        (M.singletonSub_congr
          (M.subst_congr Γ (M.repCtx Γ) (M.ctxObj Δ)
            (M.ctxToSingleton Γ) (M.ctxToSingleton Γ) f g
            (M.eqSub_refl Γ (M.repCtx Γ) (M.ctxToSingleton Γ)) h.some))
        (M.eqSub_refl (M.repCtx Δ) Δ (M.ctxFromSingleton Δ))⟩)
  left_inv := by
    intro x
    exact Quotient.inductionOn x fun σ => by
      apply Quotient.sound
      exact ⟨M.eqSub_trans Γ Δ _ _ _
        (M.compSub_congr Γ (M.repCtx Δ) Δ
          (M.singletonSub (M.contextTermDecode Γ (M.ctxObj Δ)
            (M.contextTermEncode Γ (M.ctxObj Δ) (M.contextSubToTerm Γ Δ σ))))
          (M.singletonSub (M.contextSubToTerm Γ Δ σ))
          (M.ctxFromSingleton Δ) (M.ctxFromSingleton Δ)
          (M.singletonSub_congr
            (M.contextTermDecode_encode Γ (M.ctxObj Δ) (M.contextSubToTerm Γ Δ σ)))
          (M.eqSub_refl (M.repCtx Δ) Δ (M.ctxFromSingleton Δ)))
        (M.contextTermToSub_subToTerm Γ Δ σ)⟩
  right_inv := by
    intro x
    exact Quotient.inductionOn x fun f => by
      apply Quotient.sound
      exact ⟨M.eq_trans (M.repCtx Γ) (M.ctxObj Δ) _ _ _
        (M.subst_congr (M.repCtx Γ) Γ (M.ctxObj Δ)
          (M.ctxFromSingleton Γ) (M.ctxFromSingleton Γ)
          (M.contextSubToTerm Γ Δ (M.contextTermToSub Γ Δ
            (M.contextTermDecode Γ (M.ctxObj Δ) f)))
          (M.contextTermDecode Γ (M.ctxObj Δ) f)
          (M.eqSub_refl (M.repCtx Γ) Γ (M.ctxFromSingleton Γ))
          (M.contextSubToTerm_termToSub Γ Δ (M.contextTermDecode Γ (M.ctxObj Δ) f)))
        (M.contextTermEncode_decode Γ (M.ctxObj Δ) f)⟩

/--
The model-to-syntactic-CCC comparison data supplied by the representability axiom.

For every STLC context `Γ`, `ctxObj Γ` is a single type representing that context. Consequently,
terms and substitutions modulo definitional equality are equivalent to morphisms in `M`'s
one-variable syntactic CCC out of the representing object.
-/
structure LambdaCalculusModel.ContextComparison (M : LambdaCalculusModel) where
  /-- The object of the syntactic CCC representing an STLC context. -/
  ctxObj : M.Ctx → M.Ty
  /-- Terms in context are morphisms out of the context object. -/
  termEquiv (Γ : M.Ctx) (A : M.Ty) : M.TermQuot Γ A ≃ (ctxObj Γ ⟶ A)
  /-- Substitutions are morphisms between context objects. -/
  subEquiv (Γ Δ : M.Ctx) : M.SubQuot Γ Δ ≃ (ctxObj Γ ⟶ ctxObj Δ)

/-- The context-comparison data for any representable-context lambda-calculus model. -/
def LambdaCalculusModel.contextComparison (M : LambdaCalculusModel) : M.ContextComparison where
  ctxObj := M.ctxObj
  termEquiv := M.contextTermEquiv
  subEquiv := M.contextSubEquiv

/-- The model-to-syntactic-CCC comparison proposition. -/
def LambdaCalculusModel.HasCurryHowardLambekComparison (M : LambdaCalculusModel) : Prop :=
  Nonempty (M.ContextComparison)

/-- Every `LambdaCalculusModel` has the comparison data because representability is part of the
theory. -/
def LambdaCalculusModel.hasCurryHowardLambekComparison (M : LambdaCalculusModel) :
    M.HasCurryHowardLambekComparison :=
  ⟨M.contextComparison⟩

end LambdaCalculus

end CurryHowardLambekTwoSidedStatement
