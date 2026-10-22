import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperNormalClosure

/-! The WHOLE literal upper-unitriangular defining-fixed subgroup lies
in the SAME ORIGINAL fixed source's derived subgroup in every rank at
least three, over every prime power. No small-field simplicity,
perfectness, full-unitary equality, or derived-membership premise is
supplied to this theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

set_option maxHeartbeats 800000 in
theorem wholeUpper_original_derived (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent (s + 3) q) :
    unipotentToOriginalFixed (s + 3) q g ∈ commutator (Fixed (s + 3) q) := by
  let H : Subgroup (naturalFixed (s + 3) q) :=
    (commutator (Fixed (s + 3) q)).comap (naturalFixedToOriginal q (s + 3))
  have hH : H.Normal := inferInstance
  have hR : fixedRadical q (s + 1) ≤ H := by
    intro v hv
    exact fixedRadical_original_derived q (s + 1) (by omega) ⟨v, hv⟩
  exact upper_mem_normal_of_radical_le q (s + 1) H hH hR g

set_option maxHeartbeats 800000 in
theorem originalUnipotent_le_derived (q : CFSG.PrimePower) (s : ℕ) :
    originalUnipotent (s + 3) q ≤ commutator (Fixed (s + 3) q) := by
  rintro x ⟨g, rfl⟩
  exact wholeUpper_original_derived q s g

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
