import SymmetricSubgroupAsymptotics.TernaryFourScalarFullSocles
import SymmetricSubgroupAsymptotics.TernaryFourScalarFullAction
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! The two original full-module tops with independent global sign.
Row234 retains quotient-socle capacity1 and row258 retains capacity2.
Both bindings use the exact original four permutations, including the
global inversion, and retain every original normal quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRows234And258ScalarSocles

open SemidirectProduct TernaryFourScalarDiagonalQuotient
open TernaryFourBlockPermutationGenerators
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev action {H : Type} [Group H] (b : H →* Equiv.Perm (Fin 4)) :=
  TernaryFourScalarFullAction.action (blocks b) (scalars (H := H))

abbrev blockPerm {H : Type} [Group H] (b : H →* Equiv.Perm (Fin 4)) :=
  TernaryFourScalarAugmentation.blockPerm (R := H × C2) (blocks b) (scalars (H := H))

theorem generated_range {H : Type} [Group H]
    (bH : H →* Equiv.Perm (Fin 4))
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ h : H, bH h = g.1)
    (x y : H) (hgen : Subgroup.closure ({x,y} : Set H) = ⊤)
    (generators : Fin 4 → Equiv.Perm (Fin 12))
    (h0 : TernaryFourFullModuleCoordinates.translation
      (Multiplicative.ofAdd TernaryFourFullModuleCoordinates.unitSeed) = generators 0)
    (h1 : blockPerm bH (1,Multiplicative.ofAdd 1) = generators 1)
    (h2 : blockPerm bH (x,1) = generators 2)
    (h3 : blockPerm bH (y,1) = generators 3) :
    (action bH).range = Subgroup.closure (Set.range generators) := by
  let T := Subgroup.closure (Set.range generators)
  have hx : blockPerm bH (x,1) ∈ T := by
    rw [h2]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hy : blockPerm bH (y,1) ∈ T := by
    rw [h3]
    exact Subgroup.subset_closure (Set.mem_range_self 3)
  have hevenmem (h : H) : blockPerm bH (h,1) ∈ T := by
    let f : H →* Equiv.Perm (Fin 12) := (blockPerm bH).comp (MonoidHom.inl H C2)
    have hh : h ∈ Subgroup.closure ({x,y} : Set H) := by
      rw [hgen]
      exact Subgroup.mem_top _
    change f h ∈ T
    induction hh using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    | one => simpa only [map_one] using T.one_mem
    | mul u v _ _ hu hv => simpa only [map_mul] using T.mul_mem hu hv
    | inv u _ hu => simpa only [map_inv] using T.inv_mem hu
  have hcentral (z : C2) : blockPerm bH (1,z) ∈ T := by
    have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 :=
      (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) z
    rcases hz with rfl | rfl
    · change blockPerm bH 1 ∈ T
      rw [map_one]
      exact T.one_mem
    · rw [h1]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hblocks (r : H × C2) : blockPerm bH r ∈ T := by
    have hr : r = (r.1,1)*(1,r.2) := by ext <;> simp
    rw [hr,map_mul]
    exact T.mul_mem (hevenmem r.1) (hcentral r.2)
  have ht (v : Multiplicative FullVector) :
      TernaryFourFullModuleCoordinates.translation v ∈ T := by
    apply TernaryFourScalarFullAction.all_translations_mem (blocks bH) scalars T
      (TernaryFourScalarFullSocles.even_lifts bH heven) hblocks _ v
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  apply le_antisymm
  · exact TernaryFourScalarFullAction.action_range_le (blocks bH) scalars T ht hblocks
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨inl (Multiplicative.ofAdd TernaryFourFullModuleCoordinates.unitSeed),
        (TernaryFourScalarFullAction.action_inl _ _ _).trans h0⟩
    · exact ⟨inr (1,Multiplicative.ofAdd 1),
        (TernaryFourScalarFullAction.action_inr _ _ _).trans h1⟩
    · exact ⟨inr (x,1),(TernaryFourScalarFullAction.action_inr _ _ _).trans h2⟩
    · exact ⟨inr (y,1),(TernaryFourScalarFullAction.action_inr _ _ _).trans h3⟩

abbrev A4 := alternatingGroup (Fin 4)
abbrev alternatingBlocks := (alternatingGroup (Fin 4)).subtype
abbrev symmetricBlocks := MonoidHom.id (Equiv.Perm (Fin 4))
def alternatingFirst : A4 := ⟨a,a_even⟩
def alternatingSecond : A4 := ⟨b,b_even⟩

theorem alternating_pair_generated :
    Subgroup.closure ({alternatingFirst,alternatingSecond} : Set A4) = ⊤ := by
  let K := Subgroup.closure ({alternatingFirst,alternatingSecond} : Set A4)
  have hmap : alternatingGroup (Fin 4) ≤ K.map alternatingBlocks := by
    apply alternating_generated.ge.trans
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨alternatingFirst,Subgroup.subset_closure (by simp),rfl⟩
    · exact ⟨alternatingSecond,Subgroup.subset_closure (by simp),rfl⟩
  apply top_unique
  intro g _
  obtain ⟨h,hh,he⟩ := hmap g.2
  have hzero : h = g := Subtype.ext he
  rwa [← hzero]

theorem row234_bindings :
    TernaryFourFullModuleCoordinates.translation
        (Multiplicative.ofAdd TernaryFourFullModuleCoordinates.unitSeed) = row234Generators 0 ∧
    blockPerm alternatingBlocks (1,Multiplicative.ofAdd 1) = row234Generators 1 ∧
    blockPerm alternatingBlocks (alternatingFirst,1) = row234Generators 2 ∧
    blockPerm alternatingBlocks (alternatingSecond,1) = row234Generators 3 := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row258_bindings :
    TernaryFourFullModuleCoordinates.translation
        (Multiplicative.ofAdd TernaryFourFullModuleCoordinates.unitSeed) = row258Generators 0 ∧
    blockPerm symmetricBlocks (1,Multiplicative.ofAdd 1) = row258Generators 1 ∧
    blockPerm symmetricBlocks (c,1) = row258Generators 2 ∧
    blockPerm symmetricBlocks (s,1) = row258Generators 3 := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row234_range : (action alternatingBlocks).range = Row234Top :=
  generated_range alternatingBlocks (fun g => ⟨g,rfl⟩)
    alternatingFirst alternatingSecond alternating_pair_generated row234Generators
    row234_bindings.1 row234_bindings.2.1 row234_bindings.2.2.1 row234_bindings.2.2.2

theorem row258_range : (action symmetricBlocks).range = Row258Top :=
  generated_range symmetricBlocks (fun g => ⟨g.1,rfl⟩)
    c s symmetric_generated row258Generators
    row258_bindings.1 row258_bindings.2.1 row258_bindings.2.2.1 row258_bindings.2.2.2

def row234Map : Model alternatingBlocks →* Row234Top :=
  (MulEquiv.subgroupCongr row234_range).toMonoidHom.comp (action alternatingBlocks).rangeRestrict

def row258Map : Model symmetricBlocks →* Row258Top :=
  (MulEquiv.subgroupCongr row258_range).toMonoidHom.comp (action symmetricBlocks).rangeRestrict

theorem row234Map_surjective : Function.Surjective row234Map :=
  (MulEquiv.subgroupCongr row234_range).surjective.comp
    (action alternatingBlocks).rangeRestrict_surjective

theorem row258Map_surjective : Function.Surjective row258Map :=
  (MulEquiv.subgroupCongr row258_range).surjective.comp
    (action symmetricBlocks).rangeRestrict_surjective

theorem row234_quotientSocle (N : Subgroup Row234Top) [N.Normal] :
    SocleNormalGeneratorBound (Row234Top ⧸ N) 1 := by
  apply TernaryFourScalarFullSocles.socle_of_surjective alternatingBlocks
    Subtype.val_injective (fun g => ⟨g,rfl⟩) (by decide) _ _
    ((QuotientGroup.mk' N).comp row234Map)
    ((QuotientGroup.mk'_surjective N).comp row234Map_surjective)
  · intro M hM
    letI := hM
    exact AlternatingFourCentralTwoSocles.quotientSocle M
  · intro M hM
    letI := hM
    exact TernaryScalarComplementSocles.alternating_dihedral_socle_of_surjective
      (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)

theorem row258_quotientSocle (N : Subgroup Row258Top) [N.Normal] :
    SocleNormalGeneratorBound (Row258Top ⧸ N) 2 := by
  apply TernaryFourScalarFullSocles.socle_of_surjective symmetricBlocks
    Function.injective_id (fun g => ⟨g.1,rfl⟩) (by decide) _ _
    ((QuotientGroup.mk' N).comp row258Map)
    ((QuotientGroup.mk'_surjective N).comp row258Map_surjective)
  · intro M hM
    letI := hM
    exact quotientSocle_of_product_normal_generators
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.symmetric_normal_total)
      normal_generating_singletons_of_isCyclic M
  · intro M hM
    letI := hM
    exact TernaryScalarComplementSocles.symmetric_dihedral_socle_of_surjective
      (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)

def row234_family : row234Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row234Interface.normalRegistry (fun N => by letI := N.2; exact row234_quotientSocle N.1)

def row258_family : row258Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row258Interface.normalRegistry (fun N => by letI := N.2; exact row258_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRows234And258ScalarSocles

end
