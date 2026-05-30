/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, AI assistant
-/
module

public import InternalMath.SCT.Spec
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# SCT model file

This file contains the generated SCT model interface and a quasicategory/Kan-complex model
skeleton. The concrete top-level carriers record the intended quasicategory semantics while the
full model is developed.

The current pass fills the small amount of structure that is already directly available from
mathlib: Kan complexes embed in quasicategories, `Δ[0]` is a Kan complex, identities and
composition are the ordinary maps in the full subcategory of quasicategories, and binary products of
quasicategories are quasicategories. The remaining `sorry`s are genuine semantic gaps in the
current mathlib/SCT interface: natural isomorphisms should be equivalences in functor
quasicategories, pullbacks should be homotopy/∞-categorical pullbacks, and the fibration/universe
fields require the universal cocartesian fibration and directed-univalence machinery.
-/

@[expose] public section

generate_model_interface SCT as SCTModel

open SCT CategoryTheory
open Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet

universe u

/-- Quasicategories are invariant under isomorphism of simplicial sets. -/
public lemma Quasicategory.ofIso {X Y : SSet.{u}} (e : X ≅ Y) [Quasicategory Y] :
    Quasicategory X where
  hornFilling' := by
    intro n i σ₀ h0 hn
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (S := Y) (σ₀ ≫ e.hom) h0 hn
    use σ ≫ e.inv
    simpa [Category.assoc] using congrArg (fun f => f ≫ e.inv) hσ

/-- Every standard simplex is a quasicategory, via its identification with a finite-ordinal
nerve. -/
public instance stdSimplex.quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) :=
  Quasicategory.ofIso (stdSimplex.isoNerve n)

end SSet

namespace SCTModelHelpers

universe u

/-- The terminal simplicial set is a Kan complex.

The proof uses the Quillen fibration structure on simplicial sets: the map from `Δ[0]` to the
chosen terminal simplicial set is an isomorphism because `Δ[0]` is terminal, hence it has the right
lifting property against the horn inclusions.
-/
lemma kanComplexStdSimplexZero : SSet.KanComplex (Δ[0] : SSet.{u}) := by
  rw [SSet.KanComplex]
  rw [HomotopicalAlgebra.isFibrant_iff]
  rw [SSet.modelCategoryQuillen.fibration_iff]
  haveI : IsIso (Limits.terminal.from (Δ[0] : SSet.{u})) :=
    Limits.isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ Limits.terminalIsTerminal _
  exact MorphismProperty.rlp_of_isIso SSet.modelCategoryQuillen.J _

/-- Products of quasicategories are quasicategories.

This is the pointwise product argument: an inner horn in `X × Y` is the same as compatible inner
horns in `X` and `Y`, and the two fillers combine by the cartesian product of simplicial sets.
-/
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

/-- Bundle the nerve of an ordinary category as a quasicategory. -/
public def qcatNerve (C : Type u) [Category.{u} C] : SSet.QCat.{u} :=
  ⟨CategoryTheory.nerve C, inferInstance⟩

/-- Bundle the map on nerves induced by an ordinary functor. -/
public def qcatNerveMap {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    qcatNerve C ⟶ qcatNerve D :=
  ObjectProperty.homMk (P := SSet.Quasicategory) (CategoryTheory.nerveMap F)

/-- Interpret an anima, bundled as a Kan complex, as its underlying quasicategory. -/
def animaCat (A : ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)) :
    SSet.QCat.{u} := by
  letI : SSet.KanComplex A.obj := A.property
  exact ⟨A.obj, inferInstance⟩

/-- The terminal anima is `Δ[0]`. -/
def terminalAnima : ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S) :=
  ⟨Δ[0], kanComplexStdSimplexZero⟩

/-- The unique map from a quasicategory to the terminal anima. -/
def terminalProjection (C : SSet.QCat.{u}) : C ⟶ animaCat terminalAnima :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))

/-- The initial quasicategory, realized as the nerve of the empty category. -/
def initialQCat : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} Empty)

/-- The unique map from the initial quasicategory to any quasicategory. -/
def initialMap (C : SSet.QCat.{u}) : initialQCat ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    { app := fun Δ => TypeCat.ofHom fun x => False.elim (by
        exact x.obj ⟨0, by simp⟩ |>.down.elim)
      naturality := by
        intro Δ Γ f
        ext x
        exact False.elim (by exact x.obj ⟨0, by simp⟩ |>.down.elim) }

/-- The walking arrow, modeled as the nerve of the linearly ordered category with two objects. -/
def intervalQCat : SSet.QCat.{u} :=
  qcatNerve (ULift.{u} (Fin 2))

/-- A vertex of the walking arrow as a map from `Δ[0]`. -/
def intervalVertex (i : Fin 2) : animaCat terminalAnima ⟶ intervalQCat :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SSet.yonedaEquiv.symm (CategoryTheory.ComposableArrows.mk₀ (ULift.up i)))

/-- Pullback-indexing shape for cospans, modeled by the ordinary walking cospan nerve. -/
public def pullbackShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingCospan)

/-- Pushout-indexing shape for spans, modeled by the ordinary walking span nerve. -/
public def pushoutShapeQCat : SSet.QCat.{u} :=
  qcatNerve (CategoryTheory.AsSmall.{u} Limits.WalkingSpan)

/-- Binary product of bundled quasicategories, using the cartesian product of simplicial sets. -/
def qcatProduct (C D : SSet.QCat.{u}) : SSet.QCat.{u} := by
  letI : SSet.Quasicategory C.obj := C.property
  letI : SSet.Quasicategory D.obj := D.property
  exact ⟨C.obj ⊗ D.obj, quasicategoryTensor C.obj D.obj⟩

/-- First projection from the product quasicategory. -/
def qcatProdPr1 (C D : SSet.QCat.{u}) : qcatProduct C D ⟶ C :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.fst C.obj D.obj)

/-- Second projection from the product quasicategory. -/
def qcatProdPr2 (C D : SSet.QCat.{u}) : qcatProduct C D ⟶ D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (SemiCartesianMonoidalCategory.snd C.obj D.obj)

/-- Pairing into the product quasicategory. -/
def qcatProdPair (T C D : SSet.QCat.{u}) (F : T ⟶ C) (G : T ⟶ D) :
    T ⟶ qcatProduct C D :=
  ObjectProperty.homMk (P := SSet.Quasicategory)
    (CartesianMonoidalCategory.lift F.hom G.hom)

end SCTModelHelpers

def sctModel.{u} : SCTModel.{u} where
  Anima := ObjectProperty.FullSubcategory (fun S : SSet.{u} => SSet.KanComplex S)
  SCat := SSet.QCat.{u}
  Functor C D := C ⟶ D
  /- Missing: mathlib does not yet provide the functor-quasicategory/core package needed here.
  The intended interpretation is an edge in the functor quasicategory, with natural isomorphisms
  given by equivalence edges. -/
  NatTrans := sorry
  ObjectwiseNatIsoData := sorry
  /- Missing: this should be equivalence in the ∞-category of quasicategories, not strict
  isomorphism of simplicial sets. -/
  CatEquiv := sorry
  AnimaIndexedCat := sorry
  InvertibleMorphismData := sorry
  GroupoidWitness := fun C => ULift.{u} (PLift (SSet.KanComplex C.obj))
  ExponentiableFunctor := sorry
  ContextCat := sorry
  ContextFunctor := sorry
  ContextNatIso := sorry
  ContextCatEquiv := sorry
  ContextPullbackSquare := sorry
  GroupoidalContext := sorry
  ContextMorphismCollection := sorry
  ContextObjectCollection := sorry
  IsofibrationWitness := sorry
  Adjunction := sorry
  LeftAdjointSection := sorry
  RightAdjointSection := sorry
  LeftFibrationWitness := sorry
  RightFibrationWitness := sorry
  LocallyCocartesianFibrationWitness := sorry
  LocallyCartesianFibrationWitness := sorry
  CartesianFunctorWitness := sorry
  FiberwiseInitialWitness := sorry
  FiberwiseTerminalWitness := sorry
  ContextFibration := sorry
  ContextCartesianFibrationWitness := sorry
  ContextCocartesianFibrationWitness := sorry
  LimitCone := sorry
  ColimitCocone := sorry
  HasLimitsOfShape := sorry
  HasColimitsOfShape := sorry
  DirectedUnivalenceWitness := sorry
  UniverseWitness := sorry
  SmallWitness := sorry
  SmallCocartesianFibrationWitness := sorry
  SmallFibersWitness := sorry
  RegularUniverseWitness := sorry
  ExponentiableFibrationWitness := sorry
  ConstructiveRegularUniverseWitness := sorry
  animaCat := SCTModelHelpers.animaCat
  mapAnima := sorry
  sigmaAnimaIndexed := sorry
  sigmaAnimaIndexedProjection := sorry
  idFunctor := fun C => 𝟙 C
  compFunctor := fun _ _ _ F G => F ≫ G
  idNatIso := sorry
  compNatIso := sorry
  invNatIso := sorry
  leftUnitor := sorry
  rightUnitor := sorry
  assocFunctor := sorry
  preWhiskerNatIso := sorry
  postWhiskerNatIso := sorry
  horizCompNatIso := sorry
  catEquivOfData := sorry
  catEquivForward := sorry
  catEquivBackward := sorry
  catEquivUnit := sorry
  catEquivCounit := sorry
  terminalAnima := SCTModelHelpers.terminalAnima
  terminalProjection := SCTModelHelpers.terminalProjection
  terminalUnique := sorry
  initialCat := SCTModelHelpers.initialQCat
  initialElim := SCTModelHelpers.initialMap
  initialUnique := sorry
  initialStrict := sorry
  prodCat := SCTModelHelpers.qcatProduct
  prodPr1 := SCTModelHelpers.qcatProdPr1
  prodPr2 := SCTModelHelpers.qcatProdPr2
  prodPair := SCTModelHelpers.qcatProdPair
  /- Missing: these product comparison fields are stated as `NatIso`s. They should be filled once
  `NatIso` is interpreted as equivalences in functor quasicategories. The underlying product
  quasicategory and projection/pairing maps above are already constructed. -/
  prodBeta1 := sorry
  prodBeta2 := sorry
  prodEta := sorry
  prodUniq := sorry
  /- Missing: coproduct closure for quasicategories should use the disjoint union of simplicial
  sets together with the fact that inner horns are connected. This is not currently packaged in
  mathlib. -/
  coprodCat := sorry
  coprodIn1 := sorry
  coprodIn2 := sorry
  coprodCase := sorry
  coprodBeta1 := sorry
  coprodBeta2 := sorry
  coprodEta := sorry
  coprodUniq := sorry
  /- Missing: the SCT pullback should be a homotopy/∞-categorical pullback in `Cat_∞`.
  Strict pullbacks of simplicial sets along arbitrary maps do not supply this field. -/
  pullbackCat := sorry
  pullbackPr1 := sorry
  pullbackPr2 := sorry
  pullbackComm := sorry
  pullbackLift := sorry
  pullbackBeta1 := sorry
  pullbackBeta2 := sorry
  pullbackUniq := sorry
  pullbackEta := sorry
  coprodBaseChangeForward := sorry
  coprodBaseChangeBackward := sorry
  coprodBaseChangeUnit := sorry
  coprodBaseChangeCounit := sorry
  coprodDisjointForward := sorry
  coprodDisjointBackward := sorry
  coprodDisjointUnit := sorry
  coprodDisjointCounit := sorry
  /- Missing: mathlib is expected to gain the theorem that the simplicial internal hom with
  quasicategory target is again a quasicategory. Once available, this should be the bundled
  functor quasicategory. -/
  funCat := sorry
  precompFunctor := sorry
  postcompFunctor := sorry
  evalFunctor := sorry
  curryFunctor := sorry
  uncurryFunctor := sorry
  curryBeta := sorry
  curryEta := sorry
  curryNatIso := sorry
  uncurryNatIso := sorry
  curryUncurryForward := sorry
  curryUncurryBackward := sorry
  curryUncurryUnit := sorry
  curryUncurryCounit := sorry
  intervalCat := SCTModelHelpers.intervalQCat
  intervalZero := SCTModelHelpers.intervalVertex 0
  intervalOne := SCTModelHelpers.intervalVertex 1
  /- Missing: the low-dimensional face, degeneracy, and endpoint universal-property data below
  should be transported from the usual simplex maps. -/
  simplex2Id0 := sorry
  simplex2Can := sorry
  simplex2Id1 := sorry
  simplex2Face01 := sorry
  simplex2Face12 := sorry
  simplex2Face02 := sorry
  simplex2Deg0 := sorry
  simplex2Deg1 := sorry
  simplex2Face01Zero := sorry
  simplex2Face01One := sorry
  simplex2Face12Zero := sorry
  simplex2Face12One := sorry
  simplex2Face02Zero := sorry
  simplex2Face02One := sorry
  simplex2Deg0Beta := sorry
  simplex2Deg1Beta := sorry
  functorObjectSourceCompat := sorry
  functorObjectTargetCompat := sorry
  natTransObject := sorry
  horizCompIdId := sorry
  horizCompCompComp := sorry
  horizCompLeftId := sorry
  horizCompRightId := sorry
  assocFunctorNaturality := sorry
  squareLowerTriangle := sorry
  squareUpperTriangle := sorry
  squareRestriction := sorry
  squareExtension := sorry
  squareRestrictionUnit := sorry
  squareRestrictionCounit := sorry
  segalRestriction := sorry
  segalExtension := sorry
  segalUnit := sorry
  segalCounit := sorry
  compositeSourceCompat := sorry
  compositeTargetCompat := sorry
  composeLeftUnit := sorry
  composeRightUnit := sorry
  composeAssoc := sorry
  invertibleMorphismInverse := sorry
  invertibleMorphismInverseSource := sorry
  invertibleMorphismInverseTarget := sorry
  invertibleMorphismLeftUnit := sorry
  invertibleMorphismRightUnit := sorry
  rezkEquiv := sorry
  groupoidOfAnima := fun A => ULift.up (PLift.up A.property)
  animaOfGroupoid := fun C g => ⟨C.obj, g.down.down⟩
  groupoidConstArrowFunctor := sorry
  groupoidIntervalEquiv := sorry
  animaOfGroupoidEquiv := sorry
  coreIncl := sorry
  coreUniversalPackage := sorry
  coreLiftNatIsoFromGroupoidCoherencePackage := sorry
  subcategoryPackage := sorry
  fullSubcategoryMorphismComprehensionPackage := sorry
  invertibleMorphismObjectPackage := sorry
  localizationCat := sorry
  invertingFunctorObjectPackage := sorry
  localizationFunctor := sorry
  localizationUniversalPackage := sorry
  dependentProductOverPackage := sorry
  joinCat := sorry
  joinInl := sorry
  joinInr := sorry
  joinPushoutSquare := sorry
  joinMappingOutEquiv := sorry
  joinDesc := sorry
  joinBetaLeft := sorry
  joinBetaRight := sorry
  joinDescUniq := sorry
  intervalJoinForward := sorry
  intervalJoinBackward := sorry
  intervalJoinUnit := sorry
  intervalJoinCounit := sorry
  joinDependentProductPackage := sorry
  idContextFunctor := sorry
  compContextFunctor := sorry
  idContextNatIso := sorry
  compContextNatIso := sorry
  invContextNatIso := sorry
  contextLeftUnitor := sorry
  contextRightUnitor := sorry
  contextAssocFunctor := sorry
  contextHorizCompNatIso := sorry
  contextCatEquivOfData := sorry
  contextCatEquivForward := sorry
  contextCatEquivBackward := sorry
  contextCatEquivUnit := sorry
  contextCatEquivCounit := sorry
  groupoidalContextOfAnima := sorry
  groupoidalContextOfGroupoid := sorry
  weakenContextCat := sorry
  weakenContextFunctor := sorry
  weakenContextNatIso := sorry
  weakenContextCatEquiv := sorry
  reindexContextCat := sorry
  reindexContextFunctor := sorry
  reindexContextNatIso := sorry
  reindexContextCatEquiv := sorry
  reindexContextCatId := sorry
  reindexContextCatComp := sorry
  contextTerminalCat := sorry
  contextInitialCat := sorry
  contextProdCat := sorry
  contextTerminalProjection := sorry
  contextInitialElim := sorry
  contextProdPr1 := sorry
  contextProdPr2 := sorry
  contextCoprodCat := sorry
  contextProdPair := sorry
  contextProdBeta1 := sorry
  contextProdBeta2 := sorry
  contextCoprodIn1 := sorry
  contextCoprodIn2 := sorry
  contextPullbackCat := sorry
  contextCoprodCase := sorry
  contextCoprodBeta1 := sorry
  contextCoprodBeta2 := sorry
  contextFunCat := sorry
  contextPullbackPr1 := sorry
  contextPullbackPr2 := sorry
  contextPullbackComm := sorry
  contextCoreCat := sorry
  contextSubcategory := sorry
  contextLocalization := sorry
  contextGeometricRealization := sorry
  contextJoinCat := sorry
  contextSliceCat := sorry
  sigmaCat := sorry
  sigmaPair := sorry
  sigmaDesc := sorry
  sigmaDescBeta := sorry
  sigmaDescUniq := sorry
  sigmaProjection := sorry
  sigmaLift := sorry
  sigmaTerminalUnit := sorry
  sigmaTerminalCounit := sorry
  sigmaReindexPullbackEquiv := sorry
  sigmaFunctorPullbackSquare := sorry
  sigmaSecondProjectionPullbackSquare := sorry
  sigmaPreservesPullbackEquiv := sorry
  leftAdjointSectionFunctor := sorry
  rightAdjointSectionFunctor := sorry
  directedPullbackCat := sorry
  directedPullbackPr1 := sorry
  directedPullbackPr2 := sorry
  directedPullbackArrow := sorry
  directedEval0 := sorry
  directedEval1 := sorry
  sourceFibration := sorry
  targetFibration := sorry
  sourceCartesian := sorry
  targetCocartesian := sorry
  leftFibrationEvalEquiv := sorry
  rightFibrationEvalEquiv := sorry
  baseChangeFibration := sorry
  baseChangeCartesian := sorry
  baseChangeCocartesian := sorry
  lift0Cat := sorry
  lift1Cat := sorry
  directedPullbackMapOverBase := sorry
  beckChevalleyTransformation := sorry
  idCocartesianFunctor := sorry
  compCocartesianFunctor := sorry
  adjunctionUnit := sorry
  adjunctionCounit := sorry
  leftFibrationCocartesian := sorry
  rightFibrationCartesian := sorry
  universal_left_adjoint_section := sorry
  universalLeftSectionBase := sorry
  universal_right_adjoint_section := sorry
  universalRightSectionBase := sorry
  weakenContextFibration := sorry
  pullbackShapeCat := SCTModelHelpers.pullbackShapeQCat
  pushoutShapeCat := SCTModelHelpers.pushoutShapeQCat
  locallyCocartesianOfCocartesian := sorry
  locallyCartesianOfCartesian := sorry
  coneCat := sorry
  coconeCat := sorry
  limitFunctor := sorry
  colimitFunctor := sorry
  postcompEndpointFunctorCompat := sorry
  cocartesianFunctorCategoryPackage := sorry
  universeTotalCat := sorry
  universeProjection := sorry
  universeFibration := sorry
  universeCocartesian := sorry
  universeDirectedUnivalence := sorry
  directedUnivalenceMappingEquiv := sorry
  directedUnivalenceFunctorCocartesian := sorry
  directedUnivalenceToTransformation := sorry
  smallClassifyingMap := sorry
  smallClassifyingEquiv := sorry
  smallFibrationClassifyingMap := sorry
  smallFibrationClassifyingEquiv := sorry
  cartesianFibrationExponentiable := sorry
  cocartesianFibrationExponentiable := sorry
  dependentProductTotal := sorry
  dependentProductProjection := sorry
  dependentProductFibration := sorry
  dependentProductCocartesian := sorry
  categoryUniverse := sorry
  categoryUniverseWitness := sorry
  terminalSmall := sorry
  smallProduct := sorry
  smallCoproduct := sorry
  smallPullback := sorry
  smallFunctorCategory := sorry
  smallSubcategory := sorry
  smallLocalization := sorry
  smallJoin := sorry
  smallDependentProductFibration := sorry
  smallRetract := sorry
  smallFibrationOfSmallFibers := sorry
  dependentProductSmallFibers := sorry
  smallOfSmallIntervalMap := sorry
  categoryUniverseRegular := sorry
  regularSubuniversePackage := sorry
  groupoidUniversePackage := sorry
  /- Missing: this cluster needs the universal cocartesian fibration and directed univalence;
  see Cisinski--Nguyen, `The universal coCartesian fibration`, §§7--8. -/
  directed_univalence_classifies := sorry
  isAnimaCat := fun C => PLift.{0} (SSet.KanComplex C.obj)
  anima_cat_is_anima := fun A => PLift.up A.property
  equiv_to_anima_is_anima := sorry
  sigma_anima_indexed_is_anima := sorry
  containsIdentities := sorry
  closedUnderComposition := sorry
  PreservesMorphismCollection := sorry
  LandsInObjectCollection := sorry
  InvertsMorphismCollection := sorry
  CocartesianMorphism := sorry
  CartesianMorphism := sorry
  animaIndexedFiber := sorry
  sigmaAnimaIndexedPair := sorry
  intervalZeroInitialHomContractible := sorry
  intervalOneTerminalHomContractible := sorry
  localizationInverts := sorry
  objectwiseNatIsoComponent := sorry
