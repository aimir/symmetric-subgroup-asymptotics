import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailBracketRootData
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketOriginalBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarInjection

/-! The WHOLE C/D/E fixed blocks lie in the SAME intrinsic radical R.
Ambient E6 factors are used only for positive/strict matrix support;
their individual fixedness or derived membership is not asserted.
Derived membership comes from conjugating the actual outer involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterBlocks
open CFSGTitsIntrinsicFirstLayer CFSGTitsIntrinsicMiddleRadical
open CFSGReeFFourMiddleTailBracketRootData CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourInnerBracketFixedBlocks CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourMiddlePositiveKernelIntersection CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence CFSGReeFFourOuterThreeWord
open CFSGNormTwoCoordinateFunctionalRootLeading CFSGNormTwoCoordinateRootStarInjection
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGE6GeckMiddleRootSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGGradedMatrixSubgroups CFSGGradedMatrixHighLayerProducts
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "f" => outsideHeight.toAddMonoidHom
private abbrev W := functionalWeight A hd hs hp ho f
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K
private abbrev rootUnit (K : Type) [Field K] (k : Roots A) : (Mat K)ˣ :=
  selectedRootElement A hd hs hp ho K k 1

private theorem W_eq : W=middleWeight := by
  funext j
  cases j <;> rfl

private theorem root_strict_positive (K : Type) [Field K] (k : Roots A)
    (hk : 0<f k.val) : rootUnit K k∈strictUnits W := by
  have hcut : BelowCut W (f k.val) ((rootUnit K k : Mat K)-1) :=
    (selected_functional_cut_and_leading A hd hs hp ho K f k hk 1).1
  intro i j hij
  have hh := hcut i j (by omega)
  change (rootUnit K k : Mat K) i j-(1 : Mat K) i j=0 at hh
  exact sub_eq_zero.mp hh

private theorem block_roots (K : Type) [Field K] [CharP K 2] (b : Fin 3) :
    outerBlock K b=rootUnit K (outerRoot b 0)*rootUnit K (outerRoot b 1)*
      rootUnit K (outerRoot b 2) := by
  rw [outerBlock_eq]
  rfl

private theorem block_positive (K : Type) [Field K] [CharP K 2] (b : Fin 3) :
    outerBlock K b∈Positive K := by
  have h0 : rootUnit K (outerRoot b 0)∈Positive K :=
    selected_positive_root_mem A hd hs hp ho K _ (root_properties.1 b 0).2 1
  have h1 : rootUnit K (outerRoot b 1)∈Positive K :=
    selected_positive_root_mem A hd hs hp ho K _ (root_properties.1 b 1).2 1
  have h2 : rootUnit K (outerRoot b 2)∈Positive K :=
    selected_positive_root_mem A hd hs hp ho K _ (root_properties.1 b 2).2 1
  exact Eq.mpr (congrArg (fun u : (Mat K)ˣ=>u∈Positive K) (block_roots K b))
    ((Positive K).mul_mem ((Positive K).mul_mem h0 h1) h2)

private theorem block_strict (K : Type) [Field K] [CharP K 2] (b : Fin 3) :
    outerBlock K b∈strictUnits middleWeight := by
  have hheight : ∀i : Fin 3,0<f (outerRoot b i).val := by
    intro i
    fin_cases b <;> fin_cases i <;> decide
  have hm : outerBlock K b∈strictUnits W :=
    Eq.mpr (congrArg (fun u : (Mat K)ˣ=>u∈strictUnits W) (block_roots K b))
      ((strictUnits W).mul_mem
        ((strictUnits W).mul_mem (root_strict_positive K _ (hheight 0))
          (root_strict_positive K _ (hheight 1))) (root_strict_positive K _ (hheight 2)))
  exact Eq.mp (congrArg (fun w : GeckIndex→ℤ=>outerBlock K b∈strictUnits w) W_eq) hm

private theorem raw_block_positive (m : ℕ) (b : Fin 3) :
    fixedRawHom m (actualOuterBlock m b)∈Positive (Field m) :=
  Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>u∈Positive (Field m))
    (raw_actualOuterBlock m b)) (block_positive (Field m) b)

private theorem raw_block_strict (m : ℕ) (b : Fin 3) :
    fixedRawHom m (actualOuterBlock m b)∈strictUnits middleWeight :=
  Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>u∈strictUnits middleWeight)
    (raw_actualOuterBlock m b)) (block_strict (Field m) b)

theorem actualBlock_derived (m : ℕ) (b : Fin 3) :
    actualOuterBlock m b∈commutator (originalModelFixed m) := by
  change outerConjugator m b*outerInvolution m*(outerConjugator m b)⁻¹∈_
  exact (inferInstance : (commutator (originalModelFixed m)).Normal).conj_mem
    (outerInvolution m) (outer_mem_derived m) (outerConjugator m b)

theorem actualBlock_intersection (m : ℕ) (b : Fin 3) :
    actualOuterBlock m b∈middlePositiveIntersection m := by
  have hpos : actualOuterBlock m b∈fixedPositive m := raw_block_positive m b
  exact ⟨hpos,(positive_strict_iff_opposite_positive m (actualOuterBlock m b) hpos).mp
    (raw_block_strict m b)⟩

def sourceBlock (b : Fin 3) : sourceIntersection :=
  ⟨⟨actualOuterBlock 0 b,actualBlock_derived 0 b⟩,actualBlock_intersection 0 b⟩

def radicalBlock (b : Fin 3) : middleRadical := sourceEquiv (sourceBlock b)

theorem radicalBlock_source (b : Fin 3) :
    sourceEquiv.symm (radicalBlock b)=sourceBlock b :=
  sourceEquiv.symm_apply_apply (sourceBlock b)

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterBlocks
