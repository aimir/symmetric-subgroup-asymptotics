import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveSubgroups

/-! The first nontrivial residual inclusion: after the middle peel,
the entire actual outer inversion block remains available. This uses
the proved positive conjugate subgroup and a literal source inverse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSecondInversionPeel
open CFSGOpposedSubgroupPeeling CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedBruhatCover
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourRelativeWeylInvolutions CFSGReeFFourOuterFixedInversion
open CFSGReeFFourOriginalInversionFactors

private theorem middle_fixed_inv (m : ℕ) :
    (middleFixedWeyl m)⁻¹=middleFixedWeyl m :=
  Subtype.ext (middleRelativeWeyl_inv m)

theorem outer_inversion_le_middle_remainder (m : ℕ) :
    fixedOuterInversion m ≤
      remainderPart (fixedPositive m) (fixedPositive m) (middleFixedWeyl m) := by
  have hmap : (fixedOuterInversion m).map
      (MulAut.conj (middleFixedWeyl m)).toMonoidHom ≤ fixedPositive m := by
    rw [fixedOuterInversion_eq_range]
    exact middle_conjugate_fixedOuterHom_range_le m
  intro x hx
  have hxU : x∈fixedPositive m :=
    (show x.val∈modelInversion m (outerRelativeWeyl m) from hx).1
  have hc : middleFixedWeyl m*x*(middleFixedWeyl m)⁻¹∈fixedPositive m :=
    hmap ⟨x,hx,rfl⟩
  refine ⟨hxU,?_⟩
  refine ⟨middleFixedWeyl m*x*(middleFixedWeyl m)⁻¹,hc,?_⟩
  have hsquare : middleFixedWeyl m*middleFixedWeyl m=1 := by
    simpa only [middle_fixed_inv m] using inv_mul_cancel (middleFixedWeyl m)
  change middleFixedWeyl m*(middleFixedWeyl m*x*(middleFixedWeyl m)⁻¹)*
    (middleFixedWeyl m)⁻¹=x
  calc
    _=(middleFixedWeyl m*middleFixedWeyl m)*x*
        (middleFixedWeyl m*middleFixedWeyl m)⁻¹ := by group
    _=x := by rw [hsquare]; simp

theorem second_simple_block_le_remainder (m : ℕ) :
    inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m [false]) ≤
      remainderPart (fixedPositive m) (fixedPositive m) (fixedPairedWord m [true]) := by
  have he : fixedPairedWord m [true]=middleFixedWeyl m := by
    apply Subtype.ext
    exact single_paired_word_val m true
  rw [he,simple_inversion_eq_block]
  change fixedOuterInversion m ≤ _
  exact outer_inversion_le_middle_remainder m

end SymmetricSubgroupAsymptotics.CFSGReeFFourSecondInversionPeel
