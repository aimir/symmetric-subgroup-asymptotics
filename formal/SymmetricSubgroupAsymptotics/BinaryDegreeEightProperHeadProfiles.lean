import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T26.RadicalProfiles
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.RadicalProfiles
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.RadicalProfiles
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! The already checked complete original head profiles supply the sharp
proper-normal degree-eight bound. Only finite scalar tables are inspected;
no normal state is regenerated and no stored profile is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightProperHeadProfiles

section
open BinaryCarrierNormal8T26
local instance : Group Source := BinaryMenuCayley8T26.group

/-- Sharp proper-normal cost in the same original source8T26. -/
theorem proper_normal_bound_8T26 (N : Subgroup Source) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N ≤ 2 := by
  have htable : ∀ i : Fin 27, headRank i ≤ 2 ∨ 2 ^ orderLog i = 64 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := complete N
  rw [pGroup_normalGen_eq_primeRelativeHead 2 source_isPGroup, state_head_eq]
  rcases htable i with hb | hc
  · exact hb
  · exact False.elim (hproper (Subgroup.eq_top_of_card_eq _
      ((state_card i).trans (hc.trans source_card.symm))))
end

section
open BinaryCarrierNormal8T27
local instance : Group Source := BinaryMenuCayley8T27.group

/-- Sharp proper-normal cost in the same original source8T27. -/
theorem proper_normal_bound_8T27 (N : Subgroup Source) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N ≤ 2 := by
  have htable : ∀ i : Fin 13, headRank i ≤ 2 ∨ 2 ^ orderLog i = 64 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := complete N
  rw [pGroup_normalGen_eq_primeRelativeHead 2 source_isPGroup, state_head_eq]
  rcases htable i with hb | hc
  · exact hb
  · exact False.elim (hproper (Subgroup.eq_top_of_card_eq _
      ((state_card i).trans (hc.trans source_card.symm))))
end

section
open BinaryCarrierNormal8T35
local instance : Group Source := BinaryMenuCayley8T35.group

/-- Sharp proper-normal cost in the same original source8T35. -/
theorem proper_normal_bound_8T35 (N : Subgroup Source) [N.Normal] (hproper : N ≠ ⊤) :
    MarkedC4.normalGen N ≤ 2 := by
  have htable : ∀ i : Fin 28, headRank i ≤ 2 ∨ 2 ^ orderLog i = 128 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := complete N
  rw [pGroup_normalGen_eq_primeRelativeHead 2 source_isPGroup, state_head_eq]
  rcases htable i with hb | hc
  · exact hb
  · exact False.elim (hproper (Subgroup.eq_top_of_card_eq _
      ((state_card i).trans (hc.trans source_card.symm))))
end

end SymmetricSubgroupAsymptotics.BinaryDegreeEightProperHeadProfiles
