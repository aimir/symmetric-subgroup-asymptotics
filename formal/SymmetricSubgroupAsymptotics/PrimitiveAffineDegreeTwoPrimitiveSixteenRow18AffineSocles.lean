import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements

/-! The original row18 has an exact symmetric-five frame complement.
The resulting affine normal chain proves a one-generator socle in every
literal original quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFiveFrameRepresentation
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row18.top
abbrev linearGroup := R18
abbrev linearPerm := BinaryFourAffineImage.linearPerm
abbrev translationPerm := BinaryFourAffineImage.translationPerm
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector
abbrev affineAction := BinaryFourAffineImage.action linearGroup

theorem linearPerm_hom_cycle :
    linearPerm (hom cycle) = DegreeTwoPrimitiveSixteenInterfaces.row18Generators 0 := by
  rw [hom_cycle]
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm_cycle

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row18Generators 2 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

theorem row1_le_top : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.Top ≤ Top := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top :=
  row1_le_top (PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translation_mem v)

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) : linearPerm r ∈ Top := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · rw [linearPerm_hom_cycle]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
    · rw [hom_transposition_original]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  | one => simpa only [map_one] using Top.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using Top.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using Top.inv_mem hr

theorem affineAction_range : affineAction.range = Top := by
  apply le_antisymm
  · exact BinaryFourAffineImage.action_range_le linearGroup Top translation_mem
      (fun _ hr => linearPerm_mem hr)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨hom cycle, hom_cycle_mem18⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans linearPerm_hom_cycle⟩
    · exact ⟨SemidirectProduct.inr (⟨hom transposition, hom_transposition_mem18⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans hom_transposition_original⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (BinaryFourAffineImage.action_inl _ _).trans translationPerm_firstVector⟩

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (BinaryFourAffineImage.action_injective linearGroup)).symm

theorem top_normal_total (A B : Subgroup Top) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective modelEquiv.symm.toMonoidHom modelEquiv.symm.surjective
    (AffineModel.normal_total_of_irreducible_complement
      linearGroup irreducible18 linear_normal_total18) A B hA hB

theorem topSocle_one (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_one_of_normal_total top_normal_total N.1

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  (topSocle_one N).mono (by decide)

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row18.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row18.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles
end SymmetricSubgroupAsymptotics

end
