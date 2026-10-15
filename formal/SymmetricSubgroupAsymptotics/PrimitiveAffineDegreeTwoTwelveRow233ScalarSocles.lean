import SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction
import SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Original row233 is the full sign-twisted S4 module. Its actual diagonal
kernel is cyclic and its actual augmentation quotient has the proved
normal-chain property. The resulting two-position quotient-socle bound
retains the row's original normal subgroup and quotient homomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow233ScalarSocles

open SemidirectProduct TernaryFourFullModuleCoordinates
open TernaryFourBlockPermutationGenerators
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev blocks := MonoidHom.id (Equiv.Perm (Fin 4))
abbrev scalars := TernaryFourSignedAugmentation.scalar
abbrev Model := TernaryFourScalarFullProjection.Model blocks scalars
abbrev action := TernaryFourScalarFullAction.action blocks scalars
abbrev blockPerm := TernaryFourScalarAugmentation.blockPerm blocks scalars
abbrev Top := Row233Top

def reflection : Equiv.Perm (Fin 4) := Equiv.swap 1 3

theorem translation_binding : translation (Multiplicative.ofAdd unitSeed) = row233Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem first_binding : blockPerm a = row233Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem second_binding : blockPerm b = row233Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem reflection_binding : blockPerm reflection = row233Generators 3 := by
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

theorem translation_mem (v : Multiplicative FullVector) : translation v ∈ Top := by
  apply TernaryFourScalarFullAction.all_translations_mem blocks scalars Top _ complement_mem
    (by rw [translation_binding]; exact Subgroup.subset_closure (Set.mem_range_self 0)) v
  intro g
  exact ⟨g.1,rfl,TernaryFourSignedAugmentation.scalar_even g.1 g.2⟩

theorem literal_range : action.range = Top := by
  apply le_antisymm
  · exact TernaryFourScalarFullAction.action_range_le blocks scalars Top
      translation_mem complement_mem
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨inl (Multiplicative.ofAdd unitSeed),
        (TernaryFourScalarFullAction.action_inl blocks scalars _).trans translation_binding⟩
    · exact ⟨inr a,(TernaryFourScalarFullAction.action_inr blocks scalars _).trans first_binding⟩
    · exact ⟨inr b,(TernaryFourScalarFullAction.action_inr blocks scalars _).trans second_binding⟩
    · exact ⟨inr reflection,
        (TernaryFourScalarFullAction.action_inr blocks scalars _).trans reflection_binding⟩

def modelToTop : Model →* Top :=
  (MulEquiv.subgroupCongr literal_range).toMonoidHom.comp action.rangeRestrict

theorem modelToTop_surjective : Function.Surjective modelToTop :=
  (MulEquiv.subgroupCongr literal_range).surjective.comp action.rangeRestrict_surjective

theorem model_socle_of_surjective {X : Type} [Group X]
    (rho : Model →* X) (hrho : Function.Surjective rho) : SocleNormalGeneratorBound X 2 :=
  TernaryFourScalarFullProjection.socle_two_of_augmentation_normal_total blocks scalars
    TernaryFourSignedAugmentation.normal_total rho hrho

theorem quotientSocle (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 2 :=
  model_socle_of_surjective ((QuotientGroup.mk' N).comp modelToTop)
    ((QuotientGroup.mk'_surjective N).comp modelToTop_surjective)

def family : row233Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row233Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow233ScalarSocles

end
