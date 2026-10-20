import SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationSocles

/-! The exact sign-twisted S4 augmentation image for original row178.
All four original generator identities and both range inclusions are
retained before passing to each original normal quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow178AugmentationSocles

open TernaryFourAugmentationRepresentation TernaryFourSignedAugmentation
open TernaryFourBlockPermutationGenerators SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row178Top
abbrev seed := PrimitiveAffineDegreeTwoTwelveAugmentationSocles.seed
def reflection : Equiv.Perm (Fin 4) := Equiv.swap 1 3

theorem translation_binding :
    TernaryFourAugmentationAffineImage.translationPerm (Multiplicative.ofAdd seed) =
      row178Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem first_binding : blockPerm a = row178Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem second_binding : blockPerm b = row178Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem reflection_binding : blockPerm reflection = row178Generators 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem complement_mem (g : Equiv.Perm (Fin 4)) : blockPerm g ∈ Top := by
  have ha : blockPerm a ∈ Top := by
    rw [first_binding]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hb : blockPerm b ∈ Top := by
    rw [second_binding]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hr : blockPerm reflection ∈ Top := by
    rw [reflection_binding]
    exact Subgroup.subset_closure (Set.mem_range_self 3)
  have hs : blockPerm s ∈ Top := by
    have he : b⁻¹ * reflection * b = s := by decide +kernel
    rw [← he,map_mul,map_mul,map_inv]
    exact Top.mul_mem (Top.mul_mem (Top.inv_mem hb) hr) hb
  have hc : blockPerm c ∈ Top := by
    have he : a*s = c := by decide +kernel
    rw [← he,map_mul]
    exact Top.mul_mem ha hs
  have hgen : g ∈ Subgroup.closure ({c,s} : Set (Equiv.Perm (Fin 4))) := by
    rw [symmetric_generated]
    exact Subgroup.mem_top _
  induction hgen using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hs
  | one => simpa only [map_one] using Top.one_mem
  | mul x y _ _ hx hy => simpa only [map_mul] using Top.mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using Top.inv_mem hx

theorem translation_mem (v : Multiplicative Vector) :
    TernaryFourAugmentationAffineImage.translationPerm v ∈ Top :=
  translation_mem_of_irreducible Top complement_mem seed
    PrimitiveAffineDegreeTwoTwelveAugmentationSocles.seed_ne_zero
    (by rw [translation_binding]; exact Subgroup.subset_closure (Set.mem_range_self 0)) v

theorem literal_range : action.range = Top := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    rw [← inl_left_mul_inr_right g,map_mul,action_inl,action_inr]
    exact Top.mul_mem (translation_mem g.left) (complement_mem g.right)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨inl (Multiplicative.ofAdd seed),(action_inl _).trans translation_binding⟩
    · exact ⟨inr a,(action_inr _).trans first_binding⟩
    · exact ⟨inr b,(action_inr _).trans second_binding⟩
    · exact ⟨inr reflection,(action_inr _).trans reflection_binding⟩

def modelToTop : Model →* Top :=
  (MulEquiv.subgroupCongr literal_range).toMonoidHom.comp action.rangeRestrict

theorem modelToTop_surjective : Function.Surjective modelToTop :=
  (MulEquiv.subgroupCongr literal_range).surjective.comp action.rangeRestrict_surjective

theorem quotientSocle (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 :=
  socle_of_surjective ((QuotientGroup.mk' N).comp modelToTop)
    ((QuotientGroup.mk'_surjective N).comp modelToTop_surjective)

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocle N.1

noncomputable def family : row178Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row178Interface.normalRegistry topSocle

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow178AugmentationSocles

end
