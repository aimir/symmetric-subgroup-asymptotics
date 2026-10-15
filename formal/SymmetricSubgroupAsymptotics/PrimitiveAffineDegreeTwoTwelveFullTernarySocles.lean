import SymmetricSubgroupAsymptotics.TernaryFourFullModuleSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Exact full-module images for original rows194 and231. A single original
coordinate translation and the actual A4/S4 complement generate the full
translation module, using the proved four-way invariant lattice. Every
quotient bound is composed with the original quotient homomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullTernarySocles

open TernaryFourAugmentationRepresentation TernaryFourFullModuleCoordinates
open TernaryFourBlockPermutationGenerators SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

section LiteralRange

variable (R : Subgroup LinearGroup) (hR : R ≤ hom.range) (heven : evenHom.range ≤ R)
  (g h : Equiv.Perm (Fin 4)) (hg : hom g ∈ R) (hh : hom h ∈ R)
  (hgenerated : R ≤ (Subgroup.closure ({g,h} : Set (Equiv.Perm (Fin 4)))).map hom)
  (target : Fin 3 → Equiv.Perm (Fin 12))
  (ht : translation (Multiplicative.ofAdd unitSeed) = target 0)
  (hfirst : TernaryFourAugmentationAffineImage.blockPerm g = target 1)
  (hsecond : TernaryFourAugmentationAffineImage.blockPerm h = target 2)

include hR heven hg hh hgenerated ht hfirst hsecond

theorem range_eq : (action R hR).range = Subgroup.closure (Set.range target) := by
  let H := Subgroup.closure (Set.range target)
  have hblocks (sigma : Equiv.Perm (Fin 4))
      (hsigma : sigma ∈ Subgroup.closure ({g,h} : Set (Equiv.Perm (Fin 4)))) :
      TernaryFourAugmentationAffineImage.blockPerm sigma ∈ H := by
    induction hsigma using Subgroup.closure_induction with
    | mem sigma hsigma =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hsigma
      rcases hsigma with rfl | rfl
      · rw [hfirst]
        exact Subgroup.subset_closure (Set.mem_range_self 1)
      · rw [hsecond]
        exact Subgroup.subset_closure (Set.mem_range_self 2)
    | one => simpa only [map_one] using H.one_mem
    | mul sigma tau _ _ hs ht => simpa only [map_mul] using H.mul_mem hs ht
    | inv sigma _ hs => simpa only [map_inv] using H.inv_mem hs
  have hlinear (r : R) : TernaryFourAugmentationAffineImage.blockPerm
      (TernaryFourAugmentationAffineImage.blockMap R hR r) ∈ H := by
    obtain ⟨sigma,hsigma,hsigmar⟩ := hgenerated r.2
    have he : TernaryFourAugmentationAffineImage.blockMap R hR r = sigma :=
      TernaryFourAugmentationAffineImage.hom_injective
        ((TernaryFourAugmentationAffineImage.hom_blockMap R hR r).trans hsigmar.symm)
    rw [he]
    exact hblocks sigma hsigma
  have hevenBlocks (sigma : Equiv.Perm (Fin 4)) (hsigma : sigma ∈ alternatingGroup (Fin 4)) :
      TernaryFourAugmentationAffineImage.blockPerm sigma ∈ H := by
    have hmem : hom sigma ∈ R := heven ⟨⟨sigma,hsigma⟩,rfl⟩
    have he := hlinear ⟨hom sigma,hmem⟩
    rwa [TernaryFourAugmentationAffineImage.blockMap_hom] at he
  have hfull (v : Multiplicative FullVector) : translation v ∈ H :=
    full_translation_mem H hevenBlocks
      (by rw [ht]; exact Subgroup.subset_closure (Set.mem_range_self 0)) v
  have haug (v : Multiplicative Vector) :
      TernaryFourAugmentationAffineImage.translationPerm v ∈ H := by
    rw [← augmentation_translation]
    exact hfull _
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    rw [action_apply]
    apply H.mul_mem
    · exact TernaryFourAugmentationAffineImage.action_range_le R hR H haug hlinear
        ⟨x.1,rfl⟩
    · rw [diagonal_translation]
      exact hfull _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · obtain ⟨u,z,huz⟩ := exists_augmentation_constant unitSeed
      refine ⟨(inl (Multiplicative.ofAdd u),Multiplicative.ofAdd z),?_⟩
      rw [action_translation,huz]
      exact ht
    · refine ⟨(inr (⟨hom g,hg⟩ : R),1),?_⟩
      rw [action_complement,TernaryFourAugmentationAffineImage.blockMap_hom]
      exact hfirst
    · refine ⟨(inr (⟨hom h,hh⟩ : R),1),?_⟩
      rw [action_complement,TernaryFourAugmentationAffineImage.blockMap_hom]
      exact hsecond

def modelToTop : AffineModel.Aff R × C3 →* Subgroup.closure (Set.range target) :=
  (MulEquiv.subgroupCongr
    (range_eq R hR heven g h hg hh hgenerated target ht hfirst hsecond)).toMonoidHom.comp
      (action R hR).rangeRestrict

theorem modelToTop_surjective : Function.Surjective
    (modelToTop R hR heven g h hg hh hgenerated target ht hfirst hsecond) :=
  (MulEquiv.subgroupCongr
    (range_eq R hR heven g h hg hh hgenerated target ht hfirst hsecond)).surjective.comp
      (action R hR).rangeRestrict_surjective

end LiteralRange

open PrimitiveAffineDegreeTwoTwelveAugmentationSocles

theorem row194_translation : translation (Multiplicative.ofAdd unitSeed) = row194Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row194_first : TernaryFourAugmentationAffineImage.blockPerm a = row194Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row194_second : TernaryFourAugmentationAffineImage.blockPerm b = row194Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row231_translation : translation (Multiplicative.ofAdd unitSeed) = row231Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row231_first : TernaryFourAugmentationAffineImage.blockPerm c = row231Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row231_second : TernaryFourAugmentationAffineImage.blockPerm s = row231Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

def row194Map : AffineModel.Aff alternatingLinearGroup × C3 →* Row194Top :=
  modelToTop alternatingLinearGroup even_range_le le_rfl a b
    ⟨⟨a,a_even⟩,rfl⟩ ⟨⟨b,b_even⟩,rfl⟩ even_generated row194Generators
    row194_translation row194_first row194_second

theorem row194Map_surjective : Function.Surjective row194Map :=
  modelToTop_surjective alternatingLinearGroup even_range_le le_rfl a b
    ⟨⟨a,a_even⟩,rfl⟩ ⟨⟨b,b_even⟩,rfl⟩ even_generated row194Generators
    row194_translation row194_first row194_second

def row231Map : AffineModel.Aff symmetricLinearGroup × C3 →* Row231Top :=
  modelToTop symmetricLinearGroup le_rfl even_range_le c s
    ⟨c,rfl⟩ ⟨s,rfl⟩ symmetric_generated_image row231Generators
    row231_translation row231_first row231_second

theorem row231Map_surjective : Function.Surjective row231Map :=
  modelToTop_surjective symmetricLinearGroup le_rfl even_range_le c s
    ⟨c,rfl⟩ ⟨s,rfl⟩ symmetric_generated_image row231Generators
    row231_translation row231_first row231_second

theorem row194_quotientSocle (N : Subgroup Row194Top) [N.Normal] :
    SocleNormalGeneratorBound (Row194Top ⧸ N) 2 :=
  TernaryFourFullModuleSocles.alternating_socle_of_surjective
    ((QuotientGroup.mk' N).comp row194Map)
    ((QuotientGroup.mk'_surjective N).comp row194Map_surjective)

theorem row231_quotientSocle (N : Subgroup Row231Top) [N.Normal] :
    SocleNormalGeneratorBound (Row231Top ⧸ N) 1 :=
  TernaryFourFullModuleSocles.symmetric_socle_of_surjective
    ((QuotientGroup.mk' N).comp row231Map)
    ((QuotientGroup.mk'_surjective N).comp row231Map_surjective)

def row194_family : row194Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row194Interface.normalRegistry (fun N => by letI := N.2; exact row194_quotientSocle N.1)

def row231_family : row231Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row231Interface.normalRegistry (fun N => by letI := N.2; exact row231_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullTernarySocles

end
