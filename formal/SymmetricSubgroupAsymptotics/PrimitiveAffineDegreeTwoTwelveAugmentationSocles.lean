import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Exact original quotient-socle bounds for rows133 and175. The two
literal complement generators generate A4/S4; one original nonzero
augmentation translation then recovers the entire translation kernel.
The final surjection is composed with each original quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationSocles

open TernaryFourAugmentationRepresentation TernaryFourAugmentationAffineImage
open TernaryFourBlockPermutationGenerators SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def seed : Vector := ![1,1,1]
theorem seed_ne_zero : seed ≠ 0 := by decide +kernel

section LiteralRange

variable (R : Subgroup LinearGroup) (hR : R ≤ hom.range)
  (hirr : AffineModel.Irreducible R)
  (g h : Equiv.Perm (Fin 4)) (hg : hom g ∈ R) (hh : hom h ∈ R)
  (hgenerated : R ≤ (Subgroup.closure ({g,h} : Set (Equiv.Perm (Fin 4)))).map hom)
  (target : Fin 3 → Equiv.Perm (Fin 12))
  (ht : translationPerm (Multiplicative.ofAdd seed) = target 0)
  (hfirst : blockPerm g = target 1) (hsecond : blockPerm h = target 2)

include hR hirr hg hh hgenerated ht hfirst hsecond

theorem range_eq : (action R hR).range = Subgroup.closure (Set.range target) := by
  let H := Subgroup.closure (Set.range target)
  have hblocks (σ : Equiv.Perm (Fin 4))
      (hσ : σ ∈ Subgroup.closure ({g,h} : Set (Equiv.Perm (Fin 4)))) :
      blockPerm σ ∈ H := by
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl
      · rw [hfirst]
        exact Subgroup.subset_closure (Set.mem_range_self 1)
      · rw [hsecond]
        exact Subgroup.subset_closure (Set.mem_range_self 2)
    | one => simpa only [map_one] using H.one_mem
    | mul σ τ _ _ hσ hτ => simpa only [map_mul] using H.mul_mem hσ hτ
    | inv σ _ hσ => simpa only [map_inv] using H.inv_mem hσ
  have hlinear (r : R) : blockPerm (blockMap R hR r) ∈ H := by
    obtain ⟨σ,hσ,hσr⟩ := hgenerated r.2
    have he : blockMap R hR r = σ :=
      hom_injective ((hom_blockMap R hR r).trans hσr.symm)
    rw [he]
    exact hblocks σ hσ
  have htranslation (v : Multiplicative Vector) : translationPerm v ∈ H :=
    translation_mem_of_irreducible R hR hirr H hlinear seed seed_ne_zero
      (by rw [ht]; exact Subgroup.subset_closure (Set.mem_range_self 0)) v
  apply le_antisymm
  · exact action_range_le R hR H htranslation hlinear
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨inl (Multiplicative.ofAdd seed),(action_inl R hR _).trans ht⟩
    · refine ⟨inr (⟨hom g,hg⟩ : R),?_⟩
      rw [action_inr,blockMap_hom]
      exact hfirst
    · refine ⟨inr (⟨hom h,hh⟩ : R),?_⟩
      rw [action_inr,blockMap_hom]
      exact hsecond

def modelToTop : AffineModel.Aff R →* Subgroup.closure (Set.range target) :=
  (MulEquiv.subgroupCongr
    (range_eq R hR hirr g h hg hh hgenerated target ht hfirst hsecond)).toMonoidHom.comp
      (action R hR).rangeRestrict

theorem modelToTop_surjective : Function.Surjective
    (modelToTop R hR hirr g h hg hh hgenerated target ht hfirst hsecond) :=
  (MulEquiv.subgroupCongr
    (range_eq R hR hirr g h hg hh hgenerated target ht hfirst hsecond)).surjective.comp
      (action R hR).rangeRestrict_surjective

theorem quotientSocle
    (hchain : ∀ A B : Subgroup R, A.Normal → B.Normal → A ≤ B ∨ B ≤ A)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 1 := by
  let pi := (QuotientGroup.mk' N).comp
    (modelToTop R hR hirr g h hg hh hgenerated target ht hfirst hsecond)
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective N).comp
      (modelToTop_surjective R hR hirr g h hg hh hgenerated target ht hfirst hsecond)
  exact socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective pi hpi
      (AffineModel.normal_total_of_irreducible_complement R hirr hchain))

end LiteralRange

theorem even_range_le : alternatingLinearGroup ≤ hom.range := by
  rintro _ ⟨g,rfl⟩
  exact ⟨g.1,rfl⟩

theorem even_generated : alternatingLinearGroup ≤
    (Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin 4)))).map hom := by
  rw [alternating_generated]
  rintro _ ⟨g,rfl⟩
  exact ⟨g.1,g.2,rfl⟩

theorem symmetric_generated_image : symmetricLinearGroup ≤
    (Subgroup.closure ({c,s} : Set (Equiv.Perm (Fin 4)))).map hom := by
  rw [symmetric_generated]
  rintro _ ⟨g,rfl⟩
  exact ⟨g,Subgroup.mem_top _,rfl⟩

theorem row133_translation : translationPerm (Multiplicative.ofAdd seed) = row133Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem row133_first : blockPerm a = row133Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem row133_second : blockPerm b = row133Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row175_translation : translationPerm (Multiplicative.ofAdd seed) = row175Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem row175_first : blockPerm c = row175Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel
theorem row175_second : blockPerm s = row175Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row133_range : (action alternatingLinearGroup even_range_le).range = Row133Top :=
  range_eq alternatingLinearGroup even_range_le alternating_irreducible a b
    ⟨⟨a,a_even⟩,rfl⟩ ⟨⟨b,b_even⟩,rfl⟩ even_generated row133Generators
    row133_translation row133_first row133_second

theorem row175_range : (action symmetricLinearGroup le_rfl).range = Row175Top :=
  range_eq symmetricLinearGroup le_rfl symmetric_irreducible c s
    ⟨c,rfl⟩ ⟨s,rfl⟩ symmetric_generated_image row175Generators
    row175_translation row175_first row175_second

theorem row133_quotientSocle (N : Subgroup Row133Top) [N.Normal] :
    SocleNormalGeneratorBound (Row133Top ⧸ N) 1 :=
  quotientSocle alternatingLinearGroup even_range_le alternating_irreducible a b
    ⟨⟨a,a_even⟩,rfl⟩ ⟨⟨b,b_even⟩,rfl⟩ even_generated row133Generators
    row133_translation row133_first row133_second alternating_normal_total N

theorem row175_quotientSocle (N : Subgroup Row175Top) [N.Normal] :
    SocleNormalGeneratorBound (Row175Top ⧸ N) 1 :=
  quotientSocle symmetricLinearGroup le_rfl symmetric_irreducible c s
    ⟨c,rfl⟩ ⟨s,rfl⟩ symmetric_generated_image row175Generators
    row175_translation row175_first row175_second symmetric_normal_total N

theorem row133_topSocle (N : {N : Subgroup Row133Top // N.Normal}) :
    SocleNormalGeneratorBound (Row133Top ⧸ N.1) 1 := by
  letI := N.2
  exact row133_quotientSocle N.1

theorem row175_topSocle (N : {N : Subgroup Row175Top // N.Normal}) :
    SocleNormalGeneratorBound (Row175Top ⧸ N.1) 1 := by
  letI := N.2
  exact row175_quotientSocle N.1

noncomputable def row133_family :
    row133Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row133Interface.normalRegistry row133_topSocle

noncomputable def row175_family :
    row175Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row175Interface.normalRegistry row175_topSocle

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationSocles

end
