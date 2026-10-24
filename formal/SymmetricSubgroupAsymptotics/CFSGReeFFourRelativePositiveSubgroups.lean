import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveFamilies

/-! Actual conjugate subgroups inside the original exceptional-fixed
positive subgroup. The relative elements themselves are fixed, so this
uses conjugation in the fixed group, including at m=0 before any derived
or central quotient is taken. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativePositiveFamilies
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckPositiveTwist

def outerFixedWeyl (m : ℕ) : originalModelFixed m :=
  ⟨outerRelativeWeyl m,outerRelativeWeyl_fixed m⟩

def middleFixedWeyl (m : ℕ) : originalModelFixed m :=
  ⟨middleRelativeWeyl m,middleRelativeWeyl_fixed m⟩

theorem outer_conjugate_middleFixedSubgroup_le (m : ℕ) :
    (middleFixedSubgroup m).map (MulAut.conj (outerFixedWeyl m)).toMonoidHom≤
      fixedPositive m := by
  rintro g ⟨x,hx,rfl⟩
  obtain ⟨a,b,c,d,hx⟩ := hx
  change rawHom (Field m) (outerRelativeWeyl m*x.val*(outerRelativeWeyl m)⁻¹)∈
    Positive (Field m)
  rw [←hx]
  exact rawHom_outer_conjugate_middleWord_mem_positive m a b c d

theorem middle_conjugate_fixedOuterHom_range_le (m : ℕ) :
    (fixedOuterHom m).range.map (MulAut.conj (middleFixedWeyl m)).toMonoidHom≤
      fixedPositive m := by
  rintro g ⟨x,⟨a,rfl⟩,rfl⟩
  change rawHom (Field m) (middleRelativeWeyl m*outerWord m a.toAdd*
    (middleRelativeWeyl m)⁻¹)∈Positive (Field m)
  exact rawHom_middle_conjugate_outerWord_mem_positive m a.toAdd

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveSubgroups
