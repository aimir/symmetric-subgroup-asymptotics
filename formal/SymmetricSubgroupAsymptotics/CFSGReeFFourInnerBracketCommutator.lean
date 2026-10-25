import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketInitialWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketOriginalBlocks

/-! Return the two kernel-checked root words through the faithful original
fixed-group map. Every square correction and the inner commutator belongs
to the SAME actual derived subgroup, including the exceptional parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommutator
open CFSGReeFFourInnerBracketInitialWords CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourMiddleSquareOriginalWords CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGFFourOriginalMiddleWords CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticWeylWord

private abbrev W (m : ℕ) := canonicalWord e6Data (Field m) [0,5,1]

private theorem raw_outer (m : ℕ) : fixedRawHom m (outerFixedWeyl m)=W m := by
  rw [fixedRawHom_apply]
  exact rawHom_outerRelativeWeyl m

private theorem fixedRaw_injective (m : ℕ) : Function.Injective (fixedRawHom m) := by
  intro a b h
  apply Subtype.ext
  apply rawHom_injective (Field m)
  exact h

def innerCommutator (m : ℕ) : originalModelFixed m :=
  ⁅fourCycle m,outerFixedWeyl m*fourCycle m*(outerFixedWeyl m)⁻¹⁆

def corrected (m : ℕ) : originalModelFixed m :=
  (actualMiddleBlock m 1)^2*(actualMiddleBlock m 0)^2*innerCommutator m

theorem raw_candidate (m : ℕ) :
    fixedRawHom m (candidate m)=canonicalCandidate (Field m) := by
  simp only [candidate,canonicalCandidate,map_mul,map_inv,
    raw_actualMiddleBlock,raw_actualOuterBlock]

theorem raw_innerCommutator (m : ℕ) :
    fixedRawHom m (innerCommutator m)=
      ⁅yWord (Field m),(MulAut.conj (W m)) (yWord (Field m))⁆ := by
  change fixedRawHom m ⁅fourCycle m,outerFixedWeyl m*fourCycle m*(outerFixedWeyl m)⁻¹⁆=
    ⁅yWord (Field m),W m*yWord (Field m)*(W m)⁻¹⁆
  simp only [map_commutatorElement,map_mul,map_inv,raw_outer,raw_fourCycle]

theorem raw_corrected (m : ℕ) :
    fixedRawHom m (corrected m)=canonicalCorrected (Field m) := by
  simp only [corrected,canonicalCorrected,map_mul,raw_S_square,raw_T_square,
    raw_innerCommutator]

theorem original_identity (m : ℕ) : candidate m=corrected m := by
  apply fixedRaw_injective m
  rw [raw_candidate,raw_corrected]
  exact canonical_identity (Field m)

theorem candidate_mem_derived (m : ℕ) :
    candidate m ∈ commutator (originalModelFixed m) := by
  rw [original_identity,corrected]
  apply Subgroup.mul_mem
  · exact Subgroup.mul_mem _ (middle_square_mem_derived m 1) (middle_square_mem_derived m 0)
  · exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommutator
