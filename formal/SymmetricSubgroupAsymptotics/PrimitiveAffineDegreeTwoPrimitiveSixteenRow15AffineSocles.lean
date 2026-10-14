import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements

/-! Original row15: the six-configuration deleted binary representation supplies
its actual complement and irreducibility. The original nonzero translation
then gives the full affine image and a normal chain in the original top. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinarySixDeletedRepresentation
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row15.top
abbrev linearGroup := R15
abbrev linearPerm := BinaryFourAffineImage.linearPerm
abbrev translationPerm := BinaryFourAffineImage.translationPerm
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector
abbrev affineAction := BinaryFourAffineImage.action linearGroup

theorem firstVector_ne_zero : firstVector ≠ 0 := by decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row15Generators 2 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) : linearPerm r ∈ Top := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · rw [hom15_alpha_original]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
    · rw [hom15_beta_original]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  | one => simpa only [map_one] using Top.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using Top.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using Top.inv_mem hr

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top := by
  apply BinaryFourAffineImage.translation_mem_of_irreducible
    linearGroup irreducible15 Top (fun _ hr => linearPerm_mem hr)
    firstVector firstVector_ne_zero _ v
  rw [translationPerm_firstVector]
  exact Subgroup.subset_closure (Set.mem_range_self 2)

theorem affineAction_range : affineAction.range = Top := by
  apply le_antisymm
  · exact BinaryFourAffineImage.action_range_le linearGroup Top translation_mem
      (fun _ hr => linearPerm_mem hr)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨hom15 sourceCycle, alpha_mem15⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans hom15_alpha_original⟩
    · exact ⟨SemidirectProduct.inr (⟨hom15 source15, beta_mem15⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans hom15_beta_original⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (BinaryFourAffineImage.action_inl _ _).trans translationPerm_firstVector⟩

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (BinaryFourAffineImage.action_injective linearGroup)).symm

theorem top_normal_total (A B : Subgroup Top) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective modelEquiv.symm.toMonoidHom modelEquiv.symm.surjective
    (AffineModel.normal_total_of_irreducible_complement
      linearGroup irreducible15 linear_normal_total15) A B hA hB

theorem topSocle_one (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N.1

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  (topSocle_one N).mono (by decide)

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row15.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row15.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles
end SymmetricSubgroupAsymptotics

end
