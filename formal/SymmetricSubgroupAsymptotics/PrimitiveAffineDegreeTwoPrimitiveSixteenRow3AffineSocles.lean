import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9Complements

/-! Original row3: its faithful irreducible binary affine model inherits
two ambient normal generators from its actual cyclic or metacyclic
complement. The original generators and every original normal quotient
are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourProjectiveSpread
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9Complements

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row3.top
abbrev linearGroup := R3
abbrev linearPerm := BinaryFourAffineImage.linearPerm
abbrev translationPerm := BinaryFourAffineImage.translationPerm
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector
abbrev affineAction := BinaryFourAffineImage.action linearGroup

theorem firstVector_ne_zero : firstVector ≠ 0 := by decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row3Generators 1 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) : linearPerm r ∈ Top := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  rw [map_zpow, a3_original]
  exact Top.zpow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) k

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top := by
  apply BinaryFourAffineImage.translation_mem_of_irreducible
    linearGroup irreducible3 Top (fun _ hr => linearPerm_mem hr)
    firstVector firstVector_ne_zero _ v
  rw [translationPerm_firstVector]
  exact Subgroup.subset_closure (Set.mem_range_self 1)

theorem affineAction_range : affineAction.range = Top := by
  apply le_antisymm
  · exact BinaryFourAffineImage.action_range_le linearGroup Top translation_mem
      (fun _ hr => linearPerm_mem hr)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨a3, a3_mem⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans a3_original⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (BinaryFourAffineImage.action_inl _ _).trans translationPerm_firstVector⟩

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (BinaryFourAffineImage.action_injective linearGroup)).symm

theorem top_normal_generating_pairs :
    ∀ N : Subgroup Top, N.Normal →
      ∃ x : Fin 2 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective modelEquiv.symm.toMonoidHom
    modelEquiv.symm.surjective
    (AffineModel.normal_generating_tuples_of_irreducible_complement
      linearGroup irreducible3 firstVector firstVector_ne_zero (by decide)
      normal_generating_pairs3)

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generating_pairs N.1

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row3.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row3.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles
end SymmetricSubgroupAsymptotics

end
