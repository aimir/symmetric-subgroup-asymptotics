import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements

/-! Every literal normal quotient of the original primitive-sixteen row
ten has socle normal-generator bound two. The complement bound descends
from `F₃² ⋊ D₈`, then survives the faithful irreducible binary affine layer.
The final quotient is the original permutation subgroup's literal quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row10.top
abbrev linearGroup := R10
abbrev firstVector := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.firstVector
abbrev translationPerm := BinaryFourAffineImage.translationPerm
abbrev affineAction := BinaryFourAffineImage.action linearGroup

theorem firstVector_ne_zero : firstVector ≠ 0 := by decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPrimitiveSixteenInterfaces.row10Generators 4 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translationPerm_firstVector

theorem linearPerm_mem {r : LinearGroup} (hr : r ∈ linearGroup) :
    linearPerm r ∈ Top := by
  apply BinaryFourAffineImage.linearPerm_mem_of_closure linearGenerators10 Top _ hr
  intro i
  fin_cases i
  · change linearPerm a ∈ Top
    rw [linearPerm_a_row10]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  · change linearPerm b ∈ Top
    rw [linearPerm_b_row10]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  · change linearPerm s ∈ Top
    rw [linearPerm_s_row10]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  · change linearPerm t ∈ Top
    rw [linearPerm_t_row10]
    exact Subgroup.subset_closure (Set.mem_range_self 3)

theorem translation_mem (v : Multiplicative Vector) : translationPerm v ∈ Top := by
  apply BinaryFourAffineImage.translation_mem_of_irreducible
    linearGroup irreducible10 Top (fun _ hr => linearPerm_mem hr)
    firstVector firstVector_ne_zero _ v
  rw [translationPerm_firstVector]
  exact Subgroup.subset_closure (Set.mem_range_self 4)

theorem affineAction_range : affineAction.range = Top := by
  apply le_antisymm
  · exact BinaryFourAffineImage.action_range_le linearGroup Top translation_mem
      (fun _ hr => linearPerm_mem hr)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨a, a_mem10⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans linearPerm_a_row10⟩
    · exact ⟨SemidirectProduct.inr (⟨b, b_mem10⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans linearPerm_b_row10⟩
    · exact ⟨SemidirectProduct.inr (⟨s, s_mem10⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans linearPerm_s_row10⟩
    · exact ⟨SemidirectProduct.inr (⟨t, t_mem10⟩ : linearGroup),
        (BinaryFourAffineImage.action_inr _ _).trans linearPerm_t_row10⟩
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
      linearGroup irreducible10 firstVector firstVector_ne_zero (by decide)
      normal_generating_pairs10)

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generating_pairs N.1

noncomputable def family :
    DegreeTwoPrimitiveSixteenInterfaces.row10.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoPrimitiveSixteenInterfaces.row10.normalRegistry topSocle

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles
end SymmetricSubgroupAsymptotics

end
