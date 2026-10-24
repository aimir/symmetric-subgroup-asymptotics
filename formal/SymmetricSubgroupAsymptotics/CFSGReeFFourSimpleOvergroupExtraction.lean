import SymmetricSubgroupAsymptotics.CFSGReeFFourNegativeMiddleSeedTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylUnipotentGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootWordMembership

/-! A subgroup containing the actual positive fixed group and a paired
word with nonidentity lattice action contains an actual simple relative
Weyl word. The middle extraction uses only its proved constant three-
factor identity, not an arbitrary-parameter rank-one decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleOvergroupExtraction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedWordClassification CFSGReeFFourPairedWordActions
open CFSGReeFFourPairedDescentPrefixes CFSGReeFFourPairedModelWords
open CFSGReeFFourFixedCellWordAction CFSGReeFFourOriginalWeylWords
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourMiddleFixedWords
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourMiddleWeylConstantWord
open CFSGReeFFourPositiveMatrixWordValues CFSGReeFFourNegativeMiddleSeedTransport
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells CFSGFFourE6FixedGeneratedGroup
open CFSGTwistedE6WeylChamber CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateNegativeRootWordMembership CFSGNormTwoGeckPositivePGroup
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem outer_positive (m : ℕ) :
    fixedSignedOuter m false 1∈fixedPositive m := by
  change rawHom (Field m) (signedOuterWord m false 1)∈Positive (Field m)
  simp only [signedOuterWord,map_mul,rawHom_root,folded_root_eq_orbitParameter,map_one]
  change (canonicalRoot rawData (Field m) false 0 1*
    canonicalRoot rawData (Field m) false 5 1)*canonicalRoot rawData (Field m) false 1 1∈_
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(0,1),rfl⟩)
      (Subgroup.subset_closure ⟨(5,1),rfl⟩)) (Subgroup.subset_closure ⟨(1,1),rfl⟩)

private theorem middle_positive (m : ℕ) (p : Field m×Field m) :
    fixedMiddleParameter m p∈fixedPositive m :=
  middleFixedSubgroup_le_fixedPositive m
    ⟨p.1,alpha m p.1,p.2,alpha m p.2+p.1^2*alpha m p.1,rfl⟩

private def negativeSeed (m : ℕ) (middle : Bool) : originalModelFixed m :=
  if middle then fixedMiddleWeyl m*fixedMiddleParameter m (1,0)*(fixedMiddleWeyl m)⁻¹
  else fixedSignedOuter m true 1

private theorem conjugate_seed_positive (m : ℕ) (r : List (Fin 4))
    (W : originalModelFixed m) (hW : W.val=modelWeylWord (Field m) r)
    (middle : Bool)
    (hall : ∀i∈pairedSupport middle,∀j,
      (rootAction (expandRelative r) (E6Index i)).val j≤0) :
    W*negativeSeed m middle*W⁻¹∈fixedPositive m := by
  cases middle
  · change rawHom (Field m) (W.val*signedOuterWord m true 1*W.val⁻¹)∈Positive (Field m)
    rw [hW]
    simp only [map_mul,map_inv,rawHom_modelWeylWord_relative,signedOuterWord,
      rawHom_root,folded_root_eq_orbitParameter,map_one]
    let C := (MulAut.conj (wordUnit A hs hp E6Base E6Index (Field m) (expandRelative r))).toMonoidHom
    have hroot (i : Fin 6) (hi : i∈pairedSupport false) :
        C (canonicalRoot rawData (Field m) true i 1)∈Positive (Field m) :=
      positive_negative_root_word A hd hs hp ho (Field m) (expandRelative r) i 1 (hall i hi)
    change C ((canonicalRoot rawData (Field m) true 0 1*
      canonicalRoot rawData (Field m) true 5 1)*canonicalRoot rawData (Field m) true 1 1)∈_
    rw [map_mul,map_mul]
    exact (Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem (hroot 0 (by decide)) (hroot 5 (by decide)))
      (hroot 1 (by decide))
  · change rawHom (Field m) (W.val*(middleRelativeWeyl m*fixedMiddleWord m 1 0*
        (middleRelativeWeyl m)⁻¹)*W.val⁻¹)∈Positive (Field m)
    have hvalue : fixedMiddleWord m 1 0=middleWord m 1 1 0 1 := by
      simp only [fixedMiddleWord,map_one,map_zero,one_pow,mul_one,zero_add]
    simp only [map_mul,map_inv,hW,rawHom_modelWeylWord_relative,rawHom_middleRelativeWeyl]
    rw [hvalue,rawHom_middleWord_eq_coordinate]
    apply conjugate_negative_middle_positive m (expandRelative r)
    intro i hi
    apply hall i
    rcases hi with rfl|rfl|rfl <;> decide

private theorem simple_mem_of_seed (m : ℕ) (H : Subgroup (originalModelFixed m))
    (hU : fixedPositive m≤H) (middle : Bool) (hz : negativeSeed m middle∈H) :
    fixedPairedWord m [middle]∈H := by
  cases middle
  · have hpH := hU (outer_positive m)
    have he : fixedPairedWord m [false]=fixedSignedOuter m false 1*
        fixedSignedOuter m true 1*fixedSignedOuter m false 1 := by
      have hval := fixedOuterWeyl_one_val m
      apply Subtype.ext
      have hsimple : (fixedPairedWord m [false]).val=outerRelativeWeyl m := by
        simp only [fixedPairedWord,expandPaired,pairedRelativeWord,Bool.false_eq_true,ite_false,
          List.append_nil,modelWeylWord,mul_one,outerRelativeWeyl]
      rw [hsimple,←hval]
      simp only [fixedOuterWeyl,Units.val_one,inv_one,CharTwo.neg_eq,Subgroup.coe_mul]
    rw [he]
    exact H.mul_mem (H.mul_mem hpH hz) hpH
  · have hp0 := hU (middle_positive m (0,1))
    have hp1 := hU (middle_positive m (1,1))
    have he : fixedPairedWord m [true]=fixedMiddleParameter m (0,1)*
        negativeSeed m true*fixedMiddleParameter m (1,1) := by
      apply Subtype.ext
      have hsimple : (fixedPairedWord m [true]).val=middleRelativeWeyl m := by
        simp only [fixedPairedWord,expandPaired,pairedRelativeWord,ite_true,
          List.append_nil,modelWeylWord,mul_one,middleRelativeWeyl,mul_assoc]
      rw [hsimple]
      exact middleRelativeWeyl_constant_factors m
    rw [he]
    exact H.mul_mem (H.mul_mem hp0 hz) hp1

theorem exists_simple_relative_weyl_mem (m : ℕ)
    (H : Subgroup (originalModelFixed m)) (hU : fixedPositive m≤H)
    (s : List Bool) (hW : fixedPairedWord m s∈H)
    (hne : linearAction (expandRelative (expandPaired s))≠1) :
    ∃middle : Bool,fixedPairedWord m [middle]∈H := by
  let r := expandPaired s
  have hfix : reeAutomorphism m (1*modelWeylWord (Field m) r*1)=
      1*modelWeylWord (Field m) r*1 := by
    simpa only [one_mul,mul_one] using paired_model_word_fixed m s
  have hr := fixed_cell_root_action m r 1 1
    (modelEnvelope (Field m)).one_mem (modelEnvelope (Field m)).one_mem hfix
  obtain ⟨middle,hall⟩ := exists_paired_negative_support m r hr hne
  let W := fixedPairedWord m s
  let z := negativeSeed m middle
  have hx : W*z*W⁻¹∈H := hU
    (conjugate_seed_positive m r W rfl middle hall)
  have hz : z∈H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem hW) hx) hW
    have he : W⁻¹*(W*z*W⁻¹)*W=z := by group
    exact he ▸ hh
  exact ⟨middle,simple_mem_of_seed m H hU middle hz⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleOvergroupExtraction
