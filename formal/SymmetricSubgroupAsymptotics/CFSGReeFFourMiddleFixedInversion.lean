import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleInversionCoverage

/-! The actual middle fixed inversion block is the previously
constructed two-parameter middle fixed subgroup, of cardinal q squared.
This identifies one block only, not a whole positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedInversion
open CFSGReeFFourMiddleInversionCoverage CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence

def fixedMiddleInversion (m : ℕ) : Subgroup (originalModelFixed m) :=
  (modelInversion m (middleRelativeWeyl m)).comap (originalModelFixed m).subtype

theorem fixedMiddleInversion_eq_middleFixedSubgroup (m : ℕ) :
    fixedMiddleInversion m = middleFixedSubgroup m := by
  apply le_antisymm
  · intro g hg
    exact exists_middle_parameters m g.val hg
  · intro g hg
    obtain ⟨a,b,c,d,he⟩ := hg
    change g.val ∈ modelInversion m (middleRelativeWeyl m)
    rw [←he]
    exact middleWord_mem_inversion m a b c d

theorem fixedMiddleInversion_card (m : ℕ) :
    Nat.card (fixedMiddleInversion m) = (2^(2*m+1))^2 := by
  rw [fixedMiddleInversion_eq_middleFixedSubgroup]
  exact middleFixedSubgroup_card m

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedInversion
