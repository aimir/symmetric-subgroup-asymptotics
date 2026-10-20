import SymmetricSubgroupAsymptotics.BinaryFourAugmentationPermutation
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationQuotient

/-! Exact original-source bounds for zero16 rows9 and11.
The displayed model maps onto precisely the retained generator closures.
All quotient-socle bounds therefore retain the original row and normal
subgroup, with no order-identification or normal-registry premise. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation SemidirectProduct

abbrev Top9 := DegreeTwoZeroSixteenInterfaces.row9.top
abbrev Top11 := DegreeTwoZeroSixteenInterfaces.row11.top

theorem basis1_word : translations (Multiplicative.ofAdd (basisVector 1)) =
    DegreeTwoZeroSixteenInterfaces.row9Generators 1 *
    DegreeTwoZeroSixteenInterfaces.row9Generators 3 *
    (DegreeTwoZeroSixteenInterfaces.row9Generators 1)⁻¹ *
    DegreeTwoZeroSixteenInterfaces.row9Generators 3 := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem basis0_word : translations (Multiplicative.ofAdd (basisVector 0)) =
    DegreeTwoZeroSixteenInterfaces.row9Generators 0 *
    translations (Multiplicative.ofAdd (basisVector 1)) *
    (DegreeTwoZeroSixteenInterfaces.row9Generators 0)⁻¹ := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem basis3_word : translations (Multiplicative.ofAdd (basisVector 3)) =
    DegreeTwoZeroSixteenInterfaces.row9Generators 0 *
    DegreeTwoZeroSixteenInterfaces.row9Generators 3 *
    (DegreeTwoZeroSixteenInterfaces.row9Generators 0)⁻¹ := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem basis4_word : translations (Multiplicative.ofAdd (basisVector 4)) =
    DegreeTwoZeroSixteenInterfaces.row9Generators 0 *
    translations (Multiplicative.ofAdd (basisVector 3)) *
    (DegreeTwoZeroSixteenInterfaces.row9Generators 0)⁻¹ := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem correction_word : translations (Multiplicative.ofAdd correction) =
    translations (Multiplicative.ofAdd (basisVector 0)) *
    translations (Multiplicative.ofAdd (basisVector 1)) *
    translations (Multiplicative.ofAdd (basisVector 3)) := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem common_members (H : Subgroup (Equiv.Perm (Fin 16)))
    (hg : ∀ i, DegreeTwoZeroSixteenInterfaces.row9Generators i ∈ H) :
    (∀ i : Fin 5, translations (Multiplicative.ofAdd (basisVector i.castSucc)) ∈ H) ∧
      uPerm ∈ H ∧ vPerm ∈ H ∧ cPerm ∈ H := by
  have h1 : translations (Multiplicative.ofAdd (basisVector 1)) ∈ H := by
    rw [basis1_word]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hg 1) (hg 3)) (H.inv_mem (hg 1))) (hg 3)
  have h0 : translations (Multiplicative.ofAdd (basisVector 0)) ∈ H := by
    rw [basis0_word]
    exact H.mul_mem (H.mul_mem (hg 0) h1) (H.inv_mem (hg 0))
  have h2 : translations (Multiplicative.ofAdd (basisVector 2)) ∈ H := by
    rw [original_t]
    exact hg 3
  have h3 : translations (Multiplicative.ofAdd (basisVector 3)) ∈ H := by
    rw [basis3_word]
    exact H.mul_mem (H.mul_mem (hg 0) (hg 3)) (H.inv_mem (hg 0))
  have h4 : translations (Multiplicative.ofAdd (basisVector 4)) ∈ H := by
    rw [basis4_word]
    exact H.mul_mem (H.mul_mem (hg 0) h3) (H.inv_mem (hg 0))
  have hcorr : translations (Multiplicative.ofAdd correction) ∈ H := by
    rw [correction_word]
    exact H.mul_mem (H.mul_mem h0 h1) h3
  have hc0 : translations (Multiplicative.ofAdd correction) * cPerm ∈ H := by
    rw [original_c]
    exact hg 0
  have hc : cPerm ∈ H := by
    have hh := H.mul_mem (H.inv_mem hcorr) hc0
    simpa only [inv_mul_cancel_left] using hh
  refine ⟨?_, ?_, ?_, hc⟩
  · intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rw [original_u]; exact hg 1
  · rw [original_v]; exact hg 2

theorem row9_le_range (full : Bool) : Top9 ≤ (modelPermutation full).range := by
  have ht : translations (Multiplicative.ofAdd (basisVector 2)) ∈
      (modelPermutation full).range :=
    modelTranslation_mem_range full _ (by intro h; decide +kernel)
  have hcorr : translations (Multiplicative.ofAdd correction) ∈
      (modelPermutation full).range :=
    modelTranslation_mem_range full _ (by intro h; rfl)
  have hu : uPerm ∈ (modelPermutation full).range := ⟨inr uElement, modelPermutation_u full⟩
  have hv : vPerm ∈ (modelPermutation full).range := ⟨inr vElement, modelPermutation_v full⟩
  have hc : cPerm ∈ (modelPermutation full).range := ⟨inr cElement, modelPermutation_c full⟩
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change DegreeTwoZeroSixteenInterfaces.row9Generators 0 ∈ _
    rw [← original_c]
    exact (modelPermutation full).range.mul_mem hcorr hc
  · change DegreeTwoZeroSixteenInterfaces.row9Generators 1 ∈ _
    rw [← original_u]
    exact hu
  · change DegreeTwoZeroSixteenInterfaces.row9Generators 2 ∈ _
    rw [← original_v]
    exact hv
  · change DegreeTwoZeroSixteenInterfaces.row9Generators 3 ∈ _
    rw [← original_t]
    exact ht

theorem row9_range : (modelPermutation false).range = Top9 := by
  apply le_antisymm _ (row9_le_range false)
  obtain ⟨hB, hu, hv, hc⟩ := common_members Top9
    (fun i => Subgroup.subset_closure ⟨i, rfl⟩)
  exact modelPermutation_range_le false Top9 hB (by intro h; cases h) hu hv hc

theorem row11_range : (modelPermutation true).range = Top11 := by
  apply le_antisymm
  · have hg (i : Fin 4) : DegreeTwoZeroSixteenInterfaces.row9Generators i ∈ Top11 := by
      rw [← shared_generators i]
      exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
    obtain ⟨hB, hu, hv, hc⟩ := common_members Top11 hg
    apply modelPermutation_range_le true Top11 hB ?_ hu hv hc
    intro h
    rw [original_extra]
    exact Subgroup.subset_closure ⟨4, rfl⟩
  · have hg (i : Fin 4) : DegreeTwoZeroSixteenInterfaces.row11Generators i.castSucc ∈
        (modelPermutation true).range := by
      rw [shared_generators i]
      exact row9_le_range true (Subgroup.subset_closure ⟨i, rfl⟩)
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hg 0
    · exact hg 1
    · exact hg 2
    · exact hg 3
    · change DegreeTwoZeroSixteenInterfaces.row11Generators 4 ∈ _
      rw [← original_extra]
      exact modelTranslation_mem_range true _ (by intro h; cases h)

def row9Map : Model false →* Top9 :=
  (modelPermutation false).codRestrict Top9 (fun g => by
    rw [← row9_range]
    exact ⟨g, rfl⟩)

def row11Map : Model true →* Top11 :=
  (modelPermutation true).codRestrict Top11 (fun g => by
    rw [← row11_range]
    exact ⟨g, rfl⟩)

theorem row9Map_surjective : Function.Surjective row9Map := by
  intro y
  have hy : (y : Equiv.Perm (Fin 16)) ∈ (modelPermutation false).range := by
    rw [row9_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem row11Map_surjective : Function.Surjective row11Map := by
  intro y
  have hy : (y : Equiv.Perm (Fin 16)) ∈ (modelPermutation true).range := by
    rw [row11_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem row9_socle_of_surjective {Q : Type} [Group Q]
    (pi : Top9 →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  model_socle_of_surjective false (pi.comp row9Map) (hpi.comp row9Map_surjective)

theorem row11_socle_of_surjective {Q : Type} [Group Q]
    (pi : Top11 →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  model_socle_of_surjective true (pi.comp row11Map) (hpi.comp row11Map_surjective)

theorem row9_quotientSocle (N : Subgroup Top9) [N.Normal] :
    SocleNormalGeneratorBound (Top9 ⧸ N) 2 :=
  row9_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem row11_quotientSocle (N : Subgroup Top11) [N.Normal] :
    SocleNormalGeneratorBound (Top11 ⧸ N) 2 :=
  row11_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def row9Socle : DegreeTwoZeroSixteenInterfaces.row9.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact row9_quotientSocle N.1)

def row11Socle : DegreeTwoZeroSixteenInterfaces.row11.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact row11_quotientSocle N.1)

end PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles
end SymmetricSubgroupAsymptotics

end
