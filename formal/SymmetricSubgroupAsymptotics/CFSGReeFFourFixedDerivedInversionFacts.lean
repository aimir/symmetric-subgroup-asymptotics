import SymmetricSubgroupAsymptotics.InversionSubgroupConjugateMembership
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterThreeWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterWeylInvolution

/-! Actual all-parameter inversion/derived facts. Every block projection
and Weyl equality transport takes place in an ABSTRACT Group helper. The
field parameter remains abstract, and concrete binary consumers apply
opaque semantic facts without expanding root words or block predicates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDerivedInversionFacts
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterThreeWord CFSGReeFFourOuterFixedInversion
open CFSGReeFFourMiddleFixedInversion CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourMinimalParabolics CFSGReeFFourFixedWordClassification CFSGReeFFourFixedBruhatCover

open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourFixedOuterWeylInvolution CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleFixedParameters

private theorem outer_mem_inversion (m : ℕ) :
    outerInvolution m ∈ fixedOuterInversion m := by
  rw [fixedOuterInversion_eq_range]
  exact ⟨_, rfl⟩

/-- Actual outer negative membership, with NO concrete inversion-block
projection or equality transport in this declaration. -/
theorem outer_negative (m : ℕ) :
    outerFixedWeyl m * outerInvolution m * (outerFixedWeyl m)⁻¹ ∈ fixedNegative m :=
  @InversionSubgroupConjugateMembership.conjugate_mem
    (originalModelFixed m) (inferInstance : Group (originalModelFixed m))
    (fixedPositive m) (fixedNegative m)
    (if false then fixedMiddleInversion m else fixedOuterInversion m)
    (fixedPairedWord m [false]) (outerFixedWeyl m) (outerInvolution m)
    (simple_inversion_eq_block m false) (simpleWeyl_false m) (outer_mem_inversion m)


-- Pure group transport; concrete declarations below do not build
-- model-specific Eq.rec/simp terms for normal-inf membership.
private theorem conjugate_mem_normal_inf {G : Type*} [Group G]
    (V D : Subgroup G) [D.Normal] (g s : G)
    (hs : s ∈ D) (hV : g * s * g⁻¹ ∈ V) (hi : g⁻¹ = g) :
    g * s * g ∈ V ⊓ D := by
  have h : g * s * g⁻¹ ∈ V ⊓ D :=
    ⟨hV, (inferInstance : D.Normal).conj_mem _ hs _⟩
  simpa only [hi] using h

private theorem middle_square_mem_middle (m : ℕ) :
    (fourCycle m) ^ 2 ∈ middleFixedSubgroup m := by
  have hy : fourCycle m ∈ middleFixedSubgroup m := by
    change fourCycle m ∈ (middleFixedSubgroup m : Set (originalModelFixed m))
    rw [middleFixedSubgroup_set]
    exact ⟨(1, 0), rfl⟩
  exact (middleFixedSubgroup m).pow_mem hy 2

private theorem middle_square_mem_inversion (m : ℕ) :
    (fourCycle m) ^ 2 ∈ fixedMiddleInversion m := by
  rw [fixedMiddleInversion_eq_middleFixedSubgroup]
  exact middle_square_mem_middle m

-- Exact counterpart of the checked outer-negative generic call.
private theorem middle_square_negative (m : ℕ) :
    middleFixedWeyl m * (fourCycle m) ^ 2 * (middleFixedWeyl m)⁻¹ ∈ fixedNegative m :=
  @InversionSubgroupConjugateMembership.conjugate_mem
    (originalModelFixed m) (inferInstance : Group (originalModelFixed m))
    (fixedPositive m) (fixedNegative m)
    (if true then fixedMiddleInversion m else fixedOuterInversion m)
    (fixedPairedWord m [true]) (middleFixedWeyl m) ((fourCycle m) ^ 2)
    (simple_inversion_eq_block m true) (simpleWeyl_true m) (middle_square_mem_inversion m)

private theorem middle_weyl_inv (m : ℕ) : (middleFixedWeyl m)⁻¹ = middleFixedWeyl m :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using middleWeyl_square m)

theorem outer_positive_derived (m : ℕ)
    (hxD : outerInvolution m ∈ commutator (originalModelFixed m)) :
    outerInvolution m ∈ fixedPositive m ⊓ commutator (originalModelFixed m) :=
  ⟨fixedOuterHom_range_le_fixedPositive m ⟨_, rfl⟩, hxD⟩

theorem middle_square_positive_derived (m : ℕ) :
    (fourCycle m) ^ 2 ∈ fixedPositive m ⊓ commutator (originalModelFixed m) :=
  ⟨middleFixedSubgroup_le_fixedPositive m (middle_square_mem_middle m), square_mem_derived m⟩

theorem outer_negative_derived (m : ℕ)
    (hxD : outerInvolution m ∈ commutator (originalModelFixed m)) :
    outerFixedWeyl m * outerInvolution m * outerFixedWeyl m ∈
      fixedNegative m ⊓ commutator (originalModelFixed m) :=
  @conjugate_mem_normal_inf
    (originalModelFixed m) (inferInstance : Group (originalModelFixed m))
    (fixedNegative m) (commutator (originalModelFixed m)) inferInstance
    (outerFixedWeyl m) (outerInvolution m) hxD (outer_negative m) (outer_weyl_inv m)

theorem middle_square_negative_derived (m : ℕ) :
    middleFixedWeyl m * (fourCycle m) ^ 2 * middleFixedWeyl m ∈
      fixedNegative m ⊓ commutator (originalModelFixed m) :=
  @conjugate_mem_normal_inf
    (originalModelFixed m) (inferInstance : Group (originalModelFixed m))
    (fixedNegative m) (commutator (originalModelFixed m)) inferInstance
    (middleFixedWeyl m) ((fourCycle m) ^ 2) (square_mem_derived m)
    (middle_square_negative m) (middle_weyl_inv m)

theorem middle_square_square (m : ℕ) : ((fourCycle m) ^ 2) ^ 2 = 1 := by
  simpa only [← pow_mul] using fourCycle_four m

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDerivedInversionFacts
