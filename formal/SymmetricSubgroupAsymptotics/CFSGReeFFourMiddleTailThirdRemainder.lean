import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailCommutatorSecondLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedSecondLayer

/-! A retained WHOLE original fixed-group word after the checked second
layer correction. Its actual matrix deviation starts at height three.
This does not identify the remainder with a Frattini subgroup, discard
higher terms, or assert a characteristic first-layer kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailThirdRemainder
open CFSGReeFFourMiddleTailCommutatorSecondLayer CFSGReeFFourMiddleTailBracketRootData
open CFSGReeFFourInnerBracketOriginalBlocks CFSGReeFFourInnerBracketFixedBlocks
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourOuterThreeWord CFSGReeFFourOuterFixedRoot
open CFSGReeFFourFixedModelEquivalence CFSGFFourOriginalMiddleWords
open CFSGNormTwoCoordinateFunctionalRootLeading CFSGNormTwoCoordinateRootStarInjection
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckMiddleRootSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGGradedMatrixSubgroups CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixOrderedSecondLayer CFSGGradedMatrixCommutatorSecondLayer
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

private theorem cut_strict {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (w : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : BelowCut w 1 ((u : Matrix I I K)-1)) : u∈strictUnits w := by
  intro i j hij
  have hh := hu i j (by omega)
  change (u : Matrix I I K) i j-(1 : Matrix I I K) i j=0 at hh
  exact sub_eq_zero.mp hh

private theorem cut_first_zero {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (w : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : BelowCut w 2 ((u : Matrix I I K)-1)) : firstLayer w u=0 := by
  ext i j
  change (if w i=w j+1 then ((u : Matrix I I K)-1) i j else 0)=0
  split_ifs with h
  · exact hu i j (by omega)
  · rfl

private theorem root_cut (K : Type) [Field K] (k : Roots A) (d : ℤ)
    (hdpos : 0<d) (hk : d≤f k.val) :
    BelowCut W d ((rootUnit K k : Mat K)-1) := by
  have hroot : 0<f k.val := lt_of_lt_of_le hdpos hk
  have hcut : BelowCut W (f k.val) ((rootUnit K k : Mat K)-1) :=
    (selected_functional_cut_and_leading A hd hs hp ho K f k hroot 1).1
  exact belowCut_mono W d (f k.val) _ hk hcut

private theorem outer_block_cut (K : Type) [Field K] [CharP K 2] (b : Fin 3) (d : ℤ)
    (hdpos : 0<d) (hroot : ∀i : Fin 3,d≤f (outerRoot b i).val) :
    BelowCut W d ((outerBlock K b : Mat K)-1) := by
  have h0 := root_cut K (outerRoot b 0) d hdpos (hroot 0)
  have h1 := root_cut K (outerRoot b 1) d hdpos (hroot 1)
  have h2 := root_cut K (outerRoot b 2) d hdpos (hroot 2)
  have h01 := leading_deviation_mul W d hdpos
    (rootUnit K (outerRoot b 0)) (rootUnit K (outerRoot b 1)) h0 h1
  have h012 := leading_deviation_mul W d hdpos
    (rootUnit K (outerRoot b 0)*rootUnit K (outerRoot b 1))
    (rootUnit K (outerRoot b 2)) h01.1 h2
  have hProduct : outerBlock K b=rootUnit K (outerRoot b 0)*
      rootUnit K (outerRoot b 1)*rootUnit K (outerRoot b 2) := by
    rw [outerBlock_eq]
    rfl
  exact Eq.mpr (congrArg (fun u : (Mat K)ˣ=>BelowCut W d ((u : Mat K)-1)) hProduct) h012.1

private theorem C_strict (m : ℕ) :
    fixedRawHom m (actualOuterBlock m 0)∈strictUnits W := by
  have hcut := outer_block_cut (Field m) 0 1 (by decide) (by
    intro i
    fin_cases i <;> decide)
  have hraw := raw_actualOuterBlock m 0
  exact Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>u∈strictUnits W) hraw)
    (cut_strict W _ hcut)

private theorem DE_cut (m : ℕ) :
    BelowCut W 2 ((fixedRawHom m (actualOuterBlock m 1*actualOuterBlock m 2) : Mat (Field m))-1) := by
  have hD := outer_block_cut (Field m) 1 2 (by decide) (by
    intro i
    fin_cases i <;> decide)
  have hE := outer_block_cut (Field m) 2 2 (by decide) (by
    intro i
    fin_cases i <;> decide)
  have hprod := leading_deviation_mul W 2 (by decide)
    (outerBlock (Field m) 1) (outerBlock (Field m) 2) hD hE
  have hraw : fixedRawHom m (actualOuterBlock m 1*actualOuterBlock m 2)=
      outerBlock (Field m) 1*outerBlock (Field m) 2 := by
    rw [map_mul,raw_actualOuterBlock,raw_actualOuterBlock]
  exact Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>BelowCut W 2 ((u : Mat (Field m))-1)) hraw) hprod.1

private theorem X_strict (m : ℕ) :
    fixedRawHom m (outerInvolution m)∈strictUnits W := by
  have hmid : fixedRawHom m (outerInvolution m)∈strictUnits middleWeight := by
    rw [fixedRawHom_apply]
    exact outer_raw_strict m 1
  exact Eq.mpr (congrArg (fun w : GeckIndex→ℤ=>
    fixedRawHom m (outerInvolution m)∈strictUnits w) W_eq) hmid

def correctionWord (m : ℕ) : originalModelFixed m :=
  (outerInvolution m*actualOuterBlock m 0*(outerInvolution m)⁻¹*(actualOuterBlock m 0)⁻¹)*
    (actualOuterBlock m 1*actualOuterBlock m 2)⁻¹

theorem correctionWord_height_three (m : ℕ) :
    ∀i j,middleWeight i≤middleWeight j+2→
      (fixedRawHom m (correctionWord m) : Mat (Field m)) i j=
        (1 : Mat (Field m)) i j := by
  let u := fixedRawHom m
    (outerInvolution m*actualOuterBlock m 0*(outerInvolution m)⁻¹*(actualOuterBlock m 0)⁻¹)
  let v := fixedRawHom m (actualOuterBlock m 1*actualOuterBlock m 2)
  have hu_eq : u=fixedRawHom m (outerInvolution m)*fixedRawHom m (actualOuterBlock m 0)*
      (fixedRawHom m (outerInvolution m))⁻¹*(fixedRawHom m (actualOuterBlock m 0))⁻¹ := by
    simp only [u,map_mul,map_inv]
  have hu : u∈strictUnits W := by
    rw [hu_eq]
    exact (strictUnits W).mul_mem
      ((strictUnits W).mul_mem ((strictUnits W).mul_mem (X_strict m) (C_strict m))
        ((strictUnits W).inv_mem (X_strict m))) ((strictUnits W).inv_mem (C_strict m))
  have hu0 : firstLayer W u=0 :=
    (congrArg (firstLayer W) hu_eq).trans
      (commutator_firstLayer_zero W _ _ (X_strict m) (C_strict m))
  have hvc : BelowCut W 2 ((v : Mat (Field m))-1) := DE_cut m
  have hv : v∈strictUnits W := cut_strict W v
    (belowCut_mono W 1 2 _ (by decide) hvc)
  have hv0 : firstLayer W v=0 := cut_first_zero W v hvc
  have hsecond : secondLayer W u=secondLayer W v := by
    rw [W_eq]
    exact original_commutator_secondLayer m
  have hremainder := matching_secondLayer_correction W u v hu hv hu0 hv0 hsecond
  have hstrict : u*v⁻¹∈strictUnits W :=
    (strictUnits W).mul_mem hu ((strictUnits W).inv_mem hv)
  have hi0 : firstLayer W v⁻¹=0 :=
    (firstLayer_inv W v hv).trans
      ((congrArg (fun M : Mat (Field m)=> -M) hv0).trans neg_zero)
  have hfirst : firstLayer W (u*v⁻¹)=0 :=
    (firstLayer_mul W u v⁻¹ hu ((strictUnits W).inv_mem hv)).trans
      ((congrArg₂ (fun M N : Mat (Field m)=>M+N) hu0 hi0).trans (add_zero _))
  have hhigh := height_three_of_secondLayer_zero W (u*v⁻¹) hstrict hfirst hremainder
  have hraw : fixedRawHom m (correctionWord m)=u*v⁻¹ := by
    simp only [correctionWord,map_mul,map_inv,u,v]
  intro i j hij
  have hweights : W i≤W j+2 := by simpa only [W_eq] using hij
  exact (congrArg (fun t : (Mat (Field m))ˣ=>(t : Mat (Field m)) i j) hraw).trans
    (hhigh i j hweights)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailThirdRemainder
