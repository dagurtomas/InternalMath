/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# Finite simplicial shapes for SCT

This file packages the finite indexing shapes used by the SCT model scaffolds. The simplex shapes
are represented by standard simplices and are identified with nerves of finite ordinals. The square
is the cartesian product `[1] × [1]`, identified with the nerve of the product poset. Span and
cospan shapes are ordinary mathlib walking span/cospan categories, made small with `AsSmall` and
then nervified.

The declarations here are meant to be reusable by later Segal, square, and finite-limit scaffolds.
They contain no semantic placeholders.
-/

@[expose] public section

open CategoryTheory Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace SCTFiniteShapes

universe u

/-- Quasicategories are invariant under isomorphism of simplicial sets. -/
lemma quasicategoryOfIso {X Y : SSet.{u}} (e : X ≅ Y) [SSet.Quasicategory Y] :
    SSet.Quasicategory X where
  hornFilling' := by
    intro n i σ₀ h0 hn
    obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling' (S := Y) (σ₀ ≫ e.hom) h0 hn
    use σ ≫ e.inv
    simpa [Category.assoc] using congrArg (fun f => f ≫ e.inv) hσ

/-- The standard simplex is a quasicategory. -/
lemma stdSimplexQuasicategory (n : ℕ) : SSet.Quasicategory (Δ[n] : SSet.{u}) :=
  quasicategoryOfIso (SSet.stdSimplex.isoNerve n)

/-- The `n`-simplex as a bundled quasicategory. -/
def simplex (n : ℕ) : SSet.QCat.{u} :=
  ⟨Δ[n], stdSimplexQuasicategory n⟩

/-- Map of bundled simplices induced by a morphism in the simplex category. -/
def simplexMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) : simplex m ⟶ simplex n :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (SSet.stdSimplex.map f)

@[simp]
lemma simplexMap_hom {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    (simplexMap f).hom = SSet.stdSimplex.map f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma simplexMap_id (n : ℕ) : simplexMap (𝟙 ⦋n⦌) = 𝟙 (simplex n) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.id_hom]
  exact CategoryTheory.Functor.map_id SSet.stdSimplex ⦋n⦌

@[simp]
lemma simplexMap_comp {m n k : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋n⦌ ⟶ ⦋k⦌) :
    simplexMap (f ≫ g) = simplexMap f ≫ simplexMap g := by
  apply ObjectProperty.hom_ext
  rfl

/-- The standard simplex, also identified as the nerve of the finite ordinal. -/
def simplexIsoNerve (n : ℕ) :
    (simplex.{u} n).obj ≅ CategoryTheory.nerve (ULift.{u} (Fin (n + 1))) :=
  SSet.stdSimplex.isoNerve n

/-- The point shape `[0]`. -/
abbrev point : SSet.QCat.{u} := simplex 0

/-- The walking-arrow shape `[1]`. -/
abbrev interval : SSet.QCat.{u} := simplex 1

/-- The triangle shape `[2]`. -/
abbrev triangle : SSet.QCat.{u} := simplex 2

/-- A vertex of a bundled quasicategory as a map from `[0]`. -/
def qcatPoint (C : SSet.QCat.{u}) (x : C.obj _⦋0⦌) : point ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (SSet.yonedaEquiv.symm x)

/-- The `i`th vertex inclusion `[0] → [n]`. -/
def vertex (n : ℕ) (i : Fin (n + 1)) : point.{u} ⟶ simplex n :=
  simplexMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

@[simp]
lemma vertex_comp_simplexMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    vertex.{u} m i ≫ simplexMap f = vertex n (f.toOrderHom i) := by
  apply ObjectProperty.hom_ext
  rfl

/-- The coface map skipping the `i`th vertex. -/
def coface {n : ℕ} (i : Fin (n + 2)) : simplex n ⟶ simplex (n + 1) :=
  simplexMap (SimplexCategory.δ i)

/-- The codegeneracy map identifying adjacent vertices around `i`. -/
def codegeneracy {n : ℕ} (i : Fin (n + 1)) : simplex (n + 1) ⟶ simplex n :=
  simplexMap (SimplexCategory.σ i)

/-- The unique map `[1] → [0]`. -/
def intervalDegeneracy : interval.{u} ⟶ point :=
  codegeneracy (n := 0) 0

@[simp]
lemma intervalDegeneracy_vertex_zero :
    vertex.{u} 1 0 ≫ intervalDegeneracy = 𝟙 point := by
  change simplexMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2)) ≫
    simplexMap (SimplexCategory.σ (0 : Fin 1)) = 𝟙 point
  rw [← simplexMap_comp]
  rw [show SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2) ≫
    SimplexCategory.σ (0 : Fin 1) = 𝟙 ⦋0⦌ from Subsingleton.elim _ _]
  simp

@[simp]
lemma intervalDegeneracy_vertex_one :
    vertex.{u} 1 1 ≫ intervalDegeneracy = 𝟙 point := by
  change simplexMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ (1 : Fin 2)) ≫
    simplexMap (SimplexCategory.σ (0 : Fin 1)) = 𝟙 point
  rw [← simplexMap_comp]
  rw [show SimplexCategory.const ⦋0⦌ ⦋1⦌ (1 : Fin 2) ≫
    SimplexCategory.σ (0 : Fin 1) = 𝟙 ⦋0⦌ from Subsingleton.elim _ _]
  simp

/-- The edge of `[2]` from vertex `0` to vertex `1`. -/
def simplex2Face01 : interval.{u} ⟶ triangle :=
  coface (n := 1) 2

/-- The edge of `[2]` from vertex `0` to vertex `2`. -/
def simplex2Face02 : interval.{u} ⟶ triangle :=
  coface (n := 1) 1

/-- The edge of `[2]` from vertex `1` to vertex `2`. -/
def simplex2Face12 : interval.{u} ⟶ triangle :=
  coface (n := 1) 0

@[simp]
lemma simplex2Face01_vertex_zero :
    vertex.{u} 1 0 ≫ simplex2Face01 = vertex 2 0 := by
  rw [simplex2Face01, coface, vertex_comp_simplexMap]
  rfl

@[simp]
lemma simplex2Face01_vertex_one :
    vertex.{u} 1 1 ≫ simplex2Face01 = vertex 2 1 := by
  rw [simplex2Face01, coface, vertex_comp_simplexMap]
  rfl

@[simp]
lemma simplex2Face02_vertex_zero :
    vertex.{u} 1 0 ≫ simplex2Face02 = vertex 2 0 := by
  rw [simplex2Face02, coface, vertex_comp_simplexMap]
  rfl

@[simp]
lemma simplex2Face02_vertex_one :
    vertex.{u} 1 1 ≫ simplex2Face02 = vertex 2 2 := by
  rw [simplex2Face02, coface, vertex_comp_simplexMap]
  rfl

@[simp]
lemma simplex2Face12_vertex_zero :
    vertex.{u} 1 0 ≫ simplex2Face12 = vertex 2 1 := by
  rw [simplex2Face12, coface, vertex_comp_simplexMap]
  rfl

@[simp]
lemma simplex2Face12_vertex_one :
    vertex.{u} 1 1 ≫ simplex2Face12 = vertex 2 2 := by
  rw [simplex2Face12, coface, vertex_comp_simplexMap]
  rfl

/-- Products of quasicategories are quasicategories. -/
lemma quasicategoryTensor (X Y : SSet.{u}) [SSet.Quasicategory X] [SSet.Quasicategory Y] :
    SSet.Quasicategory (X ⊗ Y) where
  hornFilling' := by
    intro n i σ₀ h0 hn
    let fstXY := SemiCartesianMonoidalCategory.fst X Y
    let sndXY := SemiCartesianMonoidalCategory.snd X Y
    obtain ⟨σX, hX⟩ :=
      SSet.Quasicategory.hornFilling' (S := X) (σ₀ ≫ fstXY) h0 hn
    obtain ⟨σY, hY⟩ :=
      SSet.Quasicategory.hornFilling' (S := Y) (σ₀ ≫ sndXY) h0 hn
    let σ : Δ[n + 2] ⟶ X ⊗ Y := CartesianMonoidalCategory.lift σX σY
    use σ
    ext m z <;> simp [σ, fstXY, sndXY, hX, hY]

/-- Binary product of bundled quasicategories. -/
def product (C D : SSet.QCat.{u}) : SSet.QCat.{u} :=
  letI : SSet.Quasicategory C.obj := C.property
  letI : SSet.Quasicategory D.obj := D.property
  ⟨C.obj ⊗ D.obj, quasicategoryTensor C.obj D.obj⟩

/-- First projection from a product quasicategory. -/
def productPr1 (C D : SSet.QCat.{u}) : product C D ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.fst C.obj D.obj)

/-- Second projection from a product quasicategory. -/
def productPr2 (C D : SSet.QCat.{u}) : product C D ⟶ D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.snd C.obj D.obj)

/-- Pairing into a product quasicategory. -/
def productPair (T C D : SSet.QCat.{u}) (F : T ⟶ C) (G : T ⟶ D) :
    T ⟶ product C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (CartesianMonoidalCategory.lift F.hom G.hom)

@[simp]
lemma productPair_pr1 (T C D : SSet.QCat.{u}) (F : T ⟶ C) (G : T ⟶ D) :
    productPair T C D F G ≫ productPr1 C D = F := by
  apply ObjectProperty.hom_ext
  exact CartesianMonoidalCategory.lift_fst F.hom G.hom

@[simp]
lemma productPair_pr2 (T C D : SSet.QCat.{u}) (F : T ⟶ C) (G : T ⟶ D) :
    productPair T C D F G ≫ productPr2 C D = G := by
  apply ObjectProperty.hom_ext
  exact CartesianMonoidalCategory.lift_snd F.hom G.hom

/-- The square shape `[1] × [1]`. -/
abbrev square : SSet.QCat.{u} := product interval interval

/-- The first coordinate projection `[1] × [1] → [1]`. -/
abbrev squarePr1 : square.{u} ⟶ interval := productPr1 interval interval

/-- The second coordinate projection `[1] × [1] → [1]`. -/
abbrev squarePr2 : square.{u} ⟶ interval := productPr2 interval interval

/-- The constant endomap of `[1]` at a chosen endpoint. -/
def intervalConst (i : Fin 2) : interval.{u} ⟶ interval :=
  intervalDegeneracy ≫ vertex 1 i

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma intervalConst_vertex_zero (i : Fin 2) :
    vertex.{u} 1 0 ≫ intervalConst i = vertex 1 i := by
  rw [intervalConst, ← Category.assoc, intervalDegeneracy_vertex_zero, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma intervalConst_vertex_one (i : Fin 2) :
    vertex.{u} 1 1 ≫ intervalConst i = vertex 1 i := by
  rw [intervalConst, ← Category.assoc, intervalDegeneracy_vertex_one, Category.id_comp]

/-- The vertex `(i,j)` of the square. -/
def squareVertex (i j : Fin 2) : point.{u} ⟶ square :=
  productPair point interval interval (vertex 1 i) (vertex 1 j)

@[simp]
lemma squareVertex_pr1 (i j : Fin 2) :
    squareVertex.{u} i j ≫ squarePr1 = vertex 1 i := by
  simp [squareVertex, squarePr1]

@[simp]
lemma squareVertex_pr2 (i j : Fin 2) :
    squareVertex.{u} i j ≫ squarePr2 = vertex 1 j := by
  simp [squareVertex, squarePr2]

/-- Horizontal edge in the square at fixed second coordinate. -/
def squareHorizontal (j : Fin 2) : interval.{u} ⟶ square :=
  productPair interval interval interval (𝟙 interval) (intervalConst j)

/-- Vertical edge in the square at fixed first coordinate. -/
def squareVertical (i : Fin 2) : interval.{u} ⟶ square :=
  productPair interval interval interval (intervalConst i) (𝟙 interval)

@[simp]
lemma squareHorizontal_pr1 (j : Fin 2) :
    squareHorizontal.{u} j ≫ squarePr1 = 𝟙 interval := by
  simp [squareHorizontal, squarePr1]

@[simp]
lemma squareHorizontal_pr2 (j : Fin 2) :
    squareHorizontal.{u} j ≫ squarePr2 = intervalConst j := by
  simp [squareHorizontal, squarePr2]

@[simp]
lemma squareVertical_pr1 (i : Fin 2) :
    squareVertical.{u} i ≫ squarePr1 = intervalConst i := by
  simp [squareVertical, squarePr1]

@[simp]
lemma squareVertical_pr2 (i : Fin 2) :
    squareVertical.{u} i ≫ squarePr2 = 𝟙 interval := by
  simp [squareVertical, squarePr2]

/-- The square also identifies with the nerve of the product poset. -/
def squareIsoNerve :
    (square.{u}).obj ≅ CategoryTheory.nerve (ULift.{u} (Fin 2 × Fin 2)) :=
  SSet.prodStdSimplex.isoNerve 1 1

/-- Bundle the nerve of an ordinary category as a quasicategory. -/
def nerveQCat (C : Type u) [Category.{u} C] : SSet.QCat.{u} :=
  ⟨CategoryTheory.nerve C, inferInstance⟩

/-- Bundle the map on nerves induced by an ordinary functor. -/
def nerveMapQCat {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    nerveQCat C ⟶ nerveQCat D :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (CategoryTheory.nerveMap F)

/-- Pullback-indexing cospan shape. -/
def cospanShape : SSet.QCat.{u} :=
  nerveQCat (CategoryTheory.AsSmall.{u} Limits.WalkingCospan)

/-- Pushout-indexing span shape. -/
def spanShape : SSet.QCat.{u} :=
  nerveQCat (CategoryTheory.AsSmall.{u} Limits.WalkingSpan)

end SCTFiniteShapes
