import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupReversePeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics

/-! The actual eight-peel geometry gives positive generation from its
two literal inversion blocks and their two actual relative Weyl words.
This is a proved factorization implication in the original fixed Model,
not a bad-character ambient simple-root generation assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourMinimalParabolics CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourMiddleFixedInversion CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOuterFixedInversion CFSGReeFFourOuterFixedRoot
open CFSGReeFFourInversionPeelingWords CFSGReeFFourInversionPeeling
open CFSGReeFFourFixedSubgroupPeeling CFSGOpposedSubgroupPeeling
open CFSGOpposedSubgroupPeelingChain CFSGOpposedSubgroupReversePeeling

theorem middle_simple_inversion_eq (m : ℕ) :
    inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m true)=middleFixedSubgroup m := by
  calc
    _=fixedMiddleInversion m := simple_inversion_eq_block m true
    _=middleFixedSubgroup m := fixedMiddleInversion_eq_middleFixedSubgroup m

theorem outer_simple_inversion_eq (m : ℕ) :
    inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m false)=(fixedOuterHom m).range := by
  calc
    _=fixedOuterInversion m := simple_inversion_eq_block m false
    _=(fixedOuterHom m).range := fixedOuterInversion_eq_range m

theorem positive_le_of_simple_inversions_and_weyls (m : ℕ) (S : Subgroup (originalModelFixed m))
    (hW : ∀b : Bool,simpleWeyl m b∈S)
    (hB : ∀b : Bool,inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)≤S) :
    fixedPositive m≤S := by
  apply positive_le_of_opposition (fixedPositive m) (fixedNegative m) S (step m true) 8
    (fixed_positive_negative_disjoint m)
  · intro j _
    exact hW (axis true j)
  · intro j _
    exact hB (axis true j)
  · intro j hj
    exact simple_block_le_residual m true ⟨j,hj⟩
  · intro j _
    exact fixed_sign_factorization m [axis true j]
  · rw [eighth_prefix_eq_opposition]
    exact (fixed_positive_image_eq_fixed_negative m).le

end SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleBlockPeelingGeneration
