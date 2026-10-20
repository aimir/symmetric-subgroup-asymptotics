import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9Complements

/-! Original row9: its faithful irreducible binary affine model inherits
two ambient normal generators from its actual cyclic or metacyclic
complement. The original generators and every original normal quotient
are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourProjectiveSpread
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9Complements

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row9.top
abbrev linearGroup := R9
abbrev linearPerm := BinaryFourAffineImage.linearPerm
abbrev translationPerm := BinaryFourAffineImage.translationPerm
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector
abbrev affineAction := BinaryFourAffineImage.action linearGroup

theorem firstVector_ne_zero : firstVector ≠ 0 := by decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row9Generators 2 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) : linearPerm r ∈ Top := by
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · rw [a9_original]
      exact Subgroup.subset_closure (Set.mem_range_self 0)
    · rw [b9_original]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  | one => simpa only [map_one] using Top.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using Top.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using Top.inv_mem hr

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top := by
  apply BinaryFourAffineImage.translation_mem_of_irreducible
    linearGroup irreducible9 Top (fun _ hr => linearPerm_mem hr)
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
    · exact ⟨SemidirectProduct.inr (⟨a9, a9_mem⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans a9_original⟩
    · exact ⟨SemidirectProduct.inr (⟨b9, b9_mem⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans b9_original⟩
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
      linearGroup irreducible9 firstVector firstVector_ne_zero (by decide)
      normal_generating_pairs9)

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generating_pairs N.1

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row9.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row9.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles
end SymmetricSubgroupAsymptotics

end
