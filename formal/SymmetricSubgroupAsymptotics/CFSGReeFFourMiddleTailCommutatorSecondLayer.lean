import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailBracketRootData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalPairBracket
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketOriginalBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedKernel
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts

/-! The degree-two correction of the WHOLE actual fixed words [x,C]
and D*E agrees. The degree-three remainder is retained. This is not an
equality of group words and does not put every higher correction in the
Frattini subgroup. No root parameter is independently declared Ree-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailCommutatorSecondLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGReeFFourMiddleTailBracketRootData CFSGReeFFourInnerBracketFixedBlocks
open CFSGNormTwoCoordinateFunctionalPairBracket CFSGNormTwoCoordinateFunctionalRootLeading
open CFSGNormTwoCoordinateRootStarInjection CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootSubgroup
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixCommutatorSecondLayer
open CFSGGradedMatrixGroupSecondLayer CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixSubgroups
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourMiddleGradedKernel
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckMiddleRootSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix
open CFSGReeFFourInnerBracketOriginalBlocks CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFieldParameters
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords
open CFSGFFourE6FixedGeneratedGroup CFSGTwistedE6GeckRelativeRootGenerated
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "f" => outsideHeight.toAddMonoidHom
private abbrev W := functionalWeight A hd hs hp ho f
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K
private abbrev E (K : Type) [Field K] (k : Roots A) : Mat K :=
  selectedFieldCoefficient A hd hs hp ho K k
private abbrev Xroot (i : Fin 3) : Roots A := E6Index (outerNode i)
private abbrev rootUnit (K : Type) [Field K] (k : Roots A) : (Mat K)ˣ :=
  selectedRootElement A hd hs hp ho K k 1

private theorem W_eq : W=middleWeight := by
  funext j
  cases j <;> rfl

private theorem Xpositive (i : Fin 3) : ∀j,0≤(Xroot i).val j := by
  intro j
  change 0≤(Pi.single (outerNode i) (1 : ℤ) : Fin 6→ℤ) j
  simp only [Pi.single_apply]
  split_ifs <;> omega

private theorem Xheight (i : Fin 3) : f (Xroot i).val=1 := by
  fin_cases i <;> rfl

private theorem Cheight (i : Fin 3) : f (outerRoot 0 i).val=1 := by
  fin_cases i <;> rfl

private theorem arrow_bracket (K : Type) [Field K] [CharP K 2] (i : Fin 6) :
    ⁅E K (Xroot (arrowLeft i)),E K (outerRoot 0 (arrowRight i))⁆=E K (arrowRoot i) := by
  have hpair : integerPairing A (Xroot (arrowLeft i)).val
      (outerRoot 0 (arrowRight i)).val= -1 := by
    have hh := cross_pairing (arrowLeft i) (arrowRight i)
    have ht : (![![1,-1,-1],![-1,1,-1],![-1,-1,0]] : Fin 3→Fin 3→ℤ)
        (arrowLeft i) (arrowRight i)= -1 := by fin_cases i <;> decide
    exact hh.trans ht
  have hr : sumRoot A hs (Xroot (arrowLeft i)) (outerRoot 0 (arrowRight i)) hpair=
      arrowRoot i := by
    apply Subtype.ext
    exact arrow_sum i
  exact (adjacent_coefficient_bracket A hd hs hp ho K f
    (Xroot (arrowLeft i)) (outerRoot 0 (arrowRight i))
    (Xpositive _) (root_properties.1 0 _).2 (Xheight _) (Cheight _) hpair).trans
      (congrArg (E K) hr)

private theorem other_bracket (K : Type) [Field K] [CharP K 2] (i j : Fin 3)
    (hij : integerPairing A (Xroot i).val (outerRoot 0 j).val=0 ∨
      integerPairing A (Xroot i).val (outerRoot 0 j).val=1) :
    ⁅E K (Xroot i),E K (outerRoot 0 j)⁆=0 :=
  nonadjacent_coefficient_bracket A hd hs hp ho K f (Xroot i) (outerRoot 0 j)
    (Xpositive i) (root_properties.1 0 j).2 (Xheight i) (Cheight j) hij

private def headX (K : Type) [Field K] : Mat K :=
  E K (Xroot 0)+E K (Xroot 1)+E K (Xroot 2)
private def headC (K : Type) [Field K] : Mat K :=
  E K (outerRoot 0 0)+E K (outerRoot 0 1)+E K (outerRoot 0 2)
private def headDE (K : Type) [Field K] : Mat K :=
  E K (outerRoot 1 0)+E K (outerRoot 1 1)+
    E K (outerRoot 2 0)+E K (outerRoot 2 1)

private theorem head_bracket (K : Type) [Field K] [CharP K 2] :
    ⁅headX K,headC K⁆=headDE K := by
  have h00 := other_bracket K 0 0 (Or.inr (cross_pairing 0 0))
  have h11 := other_bracket K 1 1 (Or.inr (cross_pairing 1 1))
  have h22 := other_bracket K 2 2 (Or.inl (cross_pairing 2 2))
  have h01 := arrow_bracket K 0
  have h10 := arrow_bracket K 1
  have h02 := arrow_bracket K 2
  have h12 := arrow_bracket K 3
  have h20 := arrow_bracket K 4
  have h21 := arrow_bracket K 5
  change ⁅E K (Xroot 0),E K (outerRoot 0 1)⁆=E K (middleRoot 1 2) at h01
  change ⁅E K (Xroot 1),E K (outerRoot 0 0)⁆=E K (middleRoot 1 2) at h10
  change ⁅E K (Xroot 0),E K (outerRoot 0 2)⁆=E K (outerRoot 2 1) at h02
  change ⁅E K (Xroot 1),E K (outerRoot 0 2)⁆=E K (outerRoot 2 0) at h12
  change ⁅E K (Xroot 2),E K (outerRoot 0 0)⁆=E K (outerRoot 1 1) at h20
  change ⁅E K (Xroot 2),E K (outerRoot 0 1)⁆=E K (outerRoot 1 0) at h21
  have hz : E K (middleRoot 1 2)+E K (middleRoot 1 2)=0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  simp only [headX,headC,add_lie,lie_add,h00,h11,h22,h01,h10,h02,h12,h20,h21,
    zero_add,add_zero]
  calc
    _=(E K (middleRoot 1 2)+E K (middleRoot 1 2))+headDE K := by unfold headDE; abel
    _=headDE K := by rw [hz,zero_add]

private theorem three_first (K : Type) [Field K]
    (a b c : Roots A) (ha : f a.val=1) (hb : f b.val=1) (hc : f c.val=1) :
    firstLayer W (rootUnit K a*rootUnit K b*rootUnit K c)=E K a+E K b+E K c := by
  have hA : rootUnit K a∈strictUnits W := root_strict A hd hs hp ho K f a ha 1
  have hB : rootUnit K b∈strictUnits W := root_strict A hd hs hp ho K f b hb 1
  have hC : rootUnit K c∈strictUnits W := root_strict A hd hs hp ho K f c hc 1
  have hfa : firstLayer W (rootUnit K a)=E K a := by
    exact (root_firstLayer A hd hs hp ho K f a ha 1).trans (one_smul K _)
  have hfb : firstLayer W (rootUnit K b)=E K b := by
    exact (root_firstLayer A hd hs hp ho K f b hb 1).trans (one_smul K _)
  have hfc : firstLayer W (rootUnit K c)=E K c := by
    exact (root_firstLayer A hd hs hp ho K f c hc 1).trans (one_smul K _)
  calc
    _=firstLayer W (rootUnit K a*rootUnit K b)+firstLayer W (rootUnit K c) :=
      firstLayer_mul W (rootUnit K a*rootUnit K b) (rootUnit K c)
        ((strictUnits W).mul_mem hA hB) hC
    _=(firstLayer W (rootUnit K a)+firstLayer W (rootUnit K b))+
        firstLayer W (rootUnit K c) :=
      congrArg (fun M : Mat K=>M+(firstLayer W (rootUnit K c) : Mat K))
        (firstLayer_mul W (rootUnit K a) (rootUnit K b) hA hB)
    _=E K a+E K b+E K c :=
      congrArg₂ (fun M N : Mat K=>M+N)
        (congrArg₂ (fun M N : Mat K=>M+N) hfa hfb) hfc

private theorem three_second (K : Type) [Field K]
    (a b c : Roots A) (ha : f a.val=2) (hb : f b.val=2) (hc : f c.val=3) :
    BelowCut W 2 (((rootUnit K a*rootUnit K b*rootUnit K c : (Mat K)ˣ) : Mat K)-1) ∧
      secondLayer W (rootUnit K a*rootUnit K b*rootUnit K c)=E K a+E K b := by
  have hA : BelowCut W 2 ((rootUnit K a : Mat K)-1) ∧
      secondLayer W (rootUnit K a)=E K a := by
    have hh := selected_functional_cut_and_leading A hd hs hp ho K f a (by rw [ha]; decide) 1
    rw [ha,one_smul] at hh
    exact hh
  have hB : BelowCut W 2 ((rootUnit K b : Mat K)-1) ∧
      secondLayer W (rootUnit K b)=E K b := by
    have hh := selected_functional_cut_and_leading A hd hs hp ho K f b (by rw [hb]; decide) 1
    rw [hb,one_smul] at hh
    exact hh
  have hC : BelowCut W 3 ((rootUnit K c : Mat K)-1) := by
    have hh := selected_functional_cut_and_leading A hd hs hp ho K f c (by rw [hc]; decide) 1
    rw [hc] at hh
    exact hh.1
  have hC2 : BelowCut W 2 ((rootUnit K c : Mat K)-1) :=
    belowCut_mono W 2 3 _ (by decide) hC
  have hz : secondLayer W (rootUnit K c)=0 := by
    ext i j
    change (if W i=W j+2 then ((rootUnit K c : Mat K)-1) i j else 0)=0
    split_ifs with h
    · exact hC i j (by omega)
    · rfl
  have hAB := leading_deviation_mul W 2 (by decide) (rootUnit K a) (rootUnit K b) hA.1 hB.1
  have hABC := leading_deviation_mul W 2 (by decide)
    (rootUnit K a*rootUnit K b) (rootUnit K c) hAB.1 hC2
  refine ⟨hABC.1,?_⟩
  calc
    _=secondLayer W (rootUnit K a*rootUnit K b)+secondLayer W (rootUnit K c) := hABC.2
    _=(secondLayer W (rootUnit K a)+secondLayer W (rootUnit K b))+
        secondLayer W (rootUnit K c) :=
      congrArg (fun M : Mat K=>M+(secondLayer W (rootUnit K c) : Mat K)) hAB.2
    _=(E K a+E K b)+(0 : Mat K) :=
      congrArg₂ (fun M N : Mat K=>M+N)
        (congrArg₂ (fun M N : Mat K=>M+N) hA.2 hB.2) hz
    _=E K a+E K b := add_zero _

private def rawX (K : Type) [Field K] : (Mat K)ˣ :=
  canonicalRoot rawData K false 0 1*canonicalRoot rawData K false 5 1*
    canonicalRoot rawData K false 1 1

private theorem rawX_roots (K : Type) [Field K] [CharP K 2] :
    rawX K=rootUnit K (Xroot 0)*rootUnit K (Xroot 1)*rootUnit K (Xroot 2) := by
  simp only [rawX,simple_one]
  rfl

private theorem rawX_strict (K : Type) [Field K] [CharP K 2] : rawX K∈strictUnits W := by
  rw [rawX_roots]
  exact (strictUnits W).mul_mem
    ((strictUnits W).mul_mem (root_strict A hd hs hp ho K f _ (Xheight 0) 1)
      (root_strict A hd hs hp ho K f _ (Xheight 1) 1))
    (root_strict A hd hs hp ho K f _ (Xheight 2) 1)

private theorem C_strict (K : Type) [Field K] [CharP K 2] : outerBlock K 0∈strictUnits W := by
  rw [outerBlock_eq]
  exact (strictUnits W).mul_mem
    ((strictUnits W).mul_mem (root_strict A hd hs hp ho K f _ (Cheight 0) 1)
      (root_strict A hd hs hp ho K f _ (Cheight 1) 1))
    (root_strict A hd hs hp ho K f _ (Cheight 2) 1)

private theorem DE_layer (K : Type) [Field K] [CharP K 2] :
    secondLayer W (outerBlock K 1*outerBlock K 2)=headDE K := by
  have hD := three_second K (outerRoot 1 0) (outerRoot 1 1) (outerRoot 1 2)
    (by rfl) (by rfl) (higher_outer_root_height 0)
  have hE := three_second K (outerRoot 2 0) (outerRoot 2 1) (outerRoot 2 2)
    (by rfl) (by rfl) (higher_outer_root_height 1)
  have hProduct : outerBlock K 1*outerBlock K 2=
      (rootUnit K (outerRoot 1 0)*rootUnit K (outerRoot 1 1)*rootUnit K (outerRoot 1 2))*
      (rootUnit K (outerRoot 2 0)*rootUnit K (outerRoot 2 1)*rootUnit K (outerRoot 2 2)) := by
    rw [outerBlock_eq K 1,outerBlock_eq K 2]
    rfl
  have hDE := leading_deviation_mul W 2 (by decide) _ _ hD.1 hE.1
  have hh : secondLayer W
      ((rootUnit K (outerRoot 1 0)*rootUnit K (outerRoot 1 1)*rootUnit K (outerRoot 1 2))*
        (rootUnit K (outerRoot 2 0)*rootUnit K (outerRoot 2 1)*rootUnit K (outerRoot 2 2)))=
      headDE K := by
    calc
      _=secondLayer W (rootUnit K (outerRoot 1 0)*rootUnit K (outerRoot 1 1)*
          rootUnit K (outerRoot 1 2))+
        secondLayer W (rootUnit K (outerRoot 2 0)*rootUnit K (outerRoot 2 1)*
          rootUnit K (outerRoot 2 2)) := hDE.2
      _=(E K (outerRoot 1 0)+E K (outerRoot 1 1))+
          (E K (outerRoot 2 0)+E K (outerRoot 2 1)) :=
        congrArg₂ (fun M N : Mat K=>M+N) hD.2 hE.2
      _=headDE K := by unfold headDE; abel
  exact (congrArg (secondLayer W) hProduct).trans hh

private theorem whole_word_secondLayer (K : Type) [Field K] [CharP K 2] :
    secondLayer middleWeight
      (rawX K*outerBlock K 0*(rawX K)⁻¹*(outerBlock K 0)⁻¹)=
        secondLayer middleWeight (outerBlock K 1*outerBlock K 2) := by
  rw [←W_eq]
  have hX : firstLayer W (rawX K)=headX K := by
    rw [rawX_roots]
    exact three_first K _ _ _ (Xheight 0) (Xheight 1) (Xheight 2)
  have hC : firstLayer W (outerBlock K 0)=headC K := by
    have hProduct : outerBlock K 0=rootUnit K (outerRoot 0 0)*
        rootUnit K (outerRoot 0 1)*rootUnit K (outerRoot 0 2) := by
      rw [outerBlock_eq]
      rfl
    exact (congrArg (firstLayer W) hProduct).trans
      (three_first K _ _ _ (Cheight 0) (Cheight 1) (Cheight 2))
  have hbr : secondLayer W
      (rawX K*outerBlock K 0*(rawX K)⁻¹*(outerBlock K 0)⁻¹)=
      ⁅firstLayer W (rawX K),firstLayer W (outerBlock K 0)⁆ :=
    commutator_secondLayer W (rawX K) (outerBlock K 0) (rawX_strict K) (C_strict K)
  exact hbr.trans ((congrArg₂ (fun M N : Mat K=>⁅M,N⁆) hX hC).trans
    ((head_bracket K).trans (DE_layer K).symm))

private theorem original_outer_raw (m : ℕ) :
    fixedRawHom m (outerInvolution m)=rawX (Field m) := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (CFSGReeFFourOuterFixedRoot.outerWord m 1)=_
  simp only [CFSGReeFFourOuterFixedRoot.outerWord,map_mul,rawHom_root,map_one,
    folded_root_eq_orbitParameter]
  rfl

theorem original_commutator_secondLayer (m : ℕ) :
    secondLayer middleWeight
      (fixedRawHom m (outerInvolution m*actualOuterBlock m 0*
        (outerInvolution m)⁻¹*(actualOuterBlock m 0)⁻¹))=
      secondLayer middleWeight (fixedRawHom m (actualOuterBlock m 1*actualOuterBlock m 2)) := by
  simpa only [map_mul,map_inv,original_outer_raw,raw_actualOuterBlock] using
    whole_word_secondLayer (Field m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailCommutatorSecondLayer
