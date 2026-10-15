import SymmetricSubgroupAsymptotics.TernaryFourDiagonalActions
import SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Five original diagonal-translation tops share one ternary-line model.
Their literal ranges and every original normal quotient retain capacities
2,1,2,1,2 on rows20,43,44,45,83 respectively. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles

open SemidirectProduct TernaryFourDiagonalActions TernaryFourBlockPermutationGenerators
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev diagonal := TernaryFourFullModuleCoordinates.diagonalPerm
abbrev A4 := alternatingGroup (Fin 4)
abbrev evenBlocks := (alternatingGroup (Fin 4)).subtype
abbrev allBlocks := MonoidHom.id (Equiv.Perm (Fin 4))
def evenFirst : A4 := ⟨a,a_even⟩
def evenSecond : A4 := ⟨b,b_even⟩
def reflection : Equiv.Perm (Fin 4) := Equiv.swap 1 3

theorem even_pair_generated : Subgroup.closure ({evenFirst,evenSecond} : Set A4) = ⊤ := by
  let K := Subgroup.closure ({evenFirst,evenSecond} : Set A4)
  have hmap : alternatingGroup (Fin 4) ≤ K.map evenBlocks := by
    apply alternating_generated.ge.trans
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨evenFirst,Subgroup.subset_closure (by simp),rfl⟩
    · exact ⟨evenSecond,Subgroup.subset_closure (by simp),rfl⟩
  apply top_unique
  intro g _
  obtain ⟨h,hh,he⟩ := hmap g.2
  have heq : h = g := Subtype.ext he
  rwa [← heq]

theorem plain_range {H : Type} [Group H] (bH : H →* Equiv.Perm (Fin 4))
    (x y : H) (hgen : Subgroup.closure ({x,y} : Set H) = ⊤)
    (g : Fin 3 → Equiv.Perm (Fin 12))
    (h0 : TernaryFourScalarAugmentation.blockPerm bH 1 x = g 0)
    (h1 : TernaryFourScalarAugmentation.blockPerm bH 1 y = g 1)
    (h2 : diagonal (Multiplicative.ofAdd 1) = g 2) :
    (action bH 1).range = Subgroup.closure (Set.range g) := by
  let T := Subgroup.closure (Set.range g)
  have hx : TernaryFourScalarAugmentation.blockPerm bH 1 x ∈ T := by
    rw [h0]; exact Subgroup.subset_closure (Set.mem_range_self 0)
  have hy : TernaryFourScalarAugmentation.blockPerm bH 1 y ∈ T := by
    rw [h1]; exact Subgroup.subset_closure (Set.mem_range_self 1)
  have ht : diagonal (Multiplicative.ofAdd 1) ∈ T := by
    rw [h2]; exact Subgroup.subset_closure (Set.mem_range_self 2)
  apply literal_range bH 1 g ![inr x,inr y,inl (Multiplicative.ofAdd 1)] _ ht
    (hom_mem_of_pair _ T x y hgen hx hy)
  intro i
  fin_cases i
  · exact (action_inr bH 1 x).trans h0
  · exact (action_inr bH 1 y).trans h1
  · exact (action_inl bH 1 _).trans h2

theorem independent_range {H : Type} [Group H] (bH : H →* Equiv.Perm (Fin 4))
    (x y : H) (hgen : Subgroup.closure ({x,y} : Set H) = ⊤)
    (g : Fin 4 → Equiv.Perm (Fin 12))
    (h0 : TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks bH)
      TernaryFourScalarDiagonalQuotient.scalars (x,1) = g 0)
    (h1 : TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks bH)
      TernaryFourScalarDiagonalQuotient.scalars (y,1) = g 1)
    (h2 : diagonal (Multiplicative.ofAdd 1) = g 2)
    (h3 : TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks bH)
      TernaryFourScalarDiagonalQuotient.scalars (1,Multiplicative.ofAdd 1) = g 3) :
    (action (TernaryFourScalarDiagonalQuotient.blocks bH)
      TernaryFourScalarDiagonalQuotient.scalars).range = Subgroup.closure (Set.range g) := by
  let T := Subgroup.closure (Set.range g)
  let f := TernaryFourScalarAugmentation.blockPerm
    (TernaryFourScalarDiagonalQuotient.blocks bH) TernaryFourScalarDiagonalQuotient.scalars
  have hx : f (x,1) ∈ T := by rw [h0]; exact Subgroup.subset_closure (Set.mem_range_self 0)
  have hy : f (y,1) ∈ T := by rw [h1]; exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hn : f (1,Multiplicative.ofAdd 1) ∈ T := by
    rw [h3]; exact Subgroup.subset_closure (Set.mem_range_self 3)
  have ht : diagonal (Multiplicative.ofAdd 1) ∈ T := by
    rw [h2]; exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hblocks (r : H × C2) : f r ∈ T := by
    have hp (h : H) : f (h,1) ∈ T :=
      hom_mem_of_pair (f.comp (MonoidHom.inl H C2)) T x y hgen hx hy h
    have hc (z : C2) : f (1,z) ∈ T := by
      have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 :=
        (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) z
      rcases hz with rfl | rfl
      · change f 1 ∈ T
        rw [map_one]
        exact T.one_mem
      · exact hn
    have hr : r = (r.1,1)*(1,r.2) := by ext <;> simp
    rw [hr,map_mul]
    exact T.mul_mem (hp r.1) (hc r.2)
  apply literal_range _ _ g
    ![inr (x,1),inr (y,1),inl (Multiplicative.ofAdd 1),inr (1,Multiplicative.ofAdd 1)]
    _ ht hblocks
  intro i
  fin_cases i
  · exact (action_inr _ _ _).trans h0
  · exact (action_inr _ _ _).trans h1
  · exact (action_inl _ _ _).trans h2
  · exact (action_inr _ _ _).trans h3

abbrev row20Action := action evenBlocks (1 : A4 →* (ZMod 3)ˣ)
abbrev row45Action := action allBlocks (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ)
abbrev row43Action := action (TernaryFourScalarDiagonalQuotient.blocks evenBlocks)
  TernaryFourScalarDiagonalQuotient.scalars
abbrev row83Action := action (TernaryFourScalarDiagonalQuotient.blocks allBlocks)
  TernaryFourScalarDiagonalQuotient.scalars
abbrev row44Action := action allBlocks TernaryFourSignedAugmentation.scalar

theorem row20_bindings :
    TernaryFourScalarAugmentation.blockPerm evenBlocks 1 evenFirst = row20Generators 0 ∧
    TernaryFourScalarAugmentation.blockPerm evenBlocks 1 evenSecond = row20Generators 1 ∧
    diagonal (Multiplicative.ofAdd 1) = row20Generators 2 := by
  refine ⟨?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row45_bindings :
    TernaryFourScalarAugmentation.blockPerm allBlocks 1 c = row45Generators 0 ∧
    TernaryFourScalarAugmentation.blockPerm allBlocks 1 s = row45Generators 1 ∧
    diagonal (Multiplicative.ofAdd 1) = row45Generators 2 := by
  refine ⟨?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row43_bindings :
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks evenBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (evenFirst,1) = row43Generators 0 ∧
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks evenBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (evenSecond,1) = row43Generators 1 ∧
    diagonal (Multiplicative.ofAdd 1) = row43Generators 2 ∧
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks evenBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (1,Multiplicative.ofAdd 1) = row43Generators 3 := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row83_bindings :
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks allBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (c,1) = row83Generators 0 ∧
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks allBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (s,1) = row83Generators 1 ∧
    diagonal (Multiplicative.ofAdd 1) = row83Generators 2 ∧
    TernaryFourScalarAugmentation.blockPerm (TernaryFourScalarDiagonalQuotient.blocks allBlocks)
      TernaryFourScalarDiagonalQuotient.scalars (1,Multiplicative.ofAdd 1) = row83Generators 3 := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row44_bindings :
    diagonal (Multiplicative.ofAdd 1) = row44Generators 0 ∧
    TernaryFourScalarAugmentation.blockPerm allBlocks TernaryFourSignedAugmentation.scalar a =
      row44Generators 1 ∧
    TernaryFourScalarAugmentation.blockPerm allBlocks TernaryFourSignedAugmentation.scalar b =
      row44Generators 2 ∧
    TernaryFourScalarAugmentation.blockPerm allBlocks TernaryFourSignedAugmentation.scalar reflection =
      row44Generators 3 := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row20_range : row20Action.range = Row20Top :=
  plain_range evenBlocks evenFirst evenSecond even_pair_generated row20Generators
    row20_bindings.1 row20_bindings.2.1 row20_bindings.2.2

theorem row45_range : row45Action.range = Row45Top :=
  plain_range allBlocks c s symmetric_generated row45Generators
    row45_bindings.1 row45_bindings.2.1 row45_bindings.2.2

theorem row43_range : row43Action.range = Row43Top :=
  independent_range evenBlocks evenFirst evenSecond even_pair_generated row43Generators
    row43_bindings.1 row43_bindings.2.1 row43_bindings.2.2.1 row43_bindings.2.2.2

theorem row83_range : row83Action.range = Row83Top :=
  independent_range allBlocks c s symmetric_generated row83Generators
    row83_bindings.1 row83_bindings.2.1 row83_bindings.2.2.1 row83_bindings.2.2.2

theorem row44_range : row44Action.range = Row44Top := by
  let f := TernaryFourScalarAugmentation.blockPerm allBlocks TernaryFourSignedAugmentation.scalar
  have ht : diagonal (Multiplicative.ofAdd 1) ∈ Row44Top := by
    rw [row44_bindings.1]; exact Subgroup.subset_closure (Set.mem_range_self 0)
  have ha : f a ∈ Row44Top := by
    rw [row44_bindings.2.1]; exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hb : f b ∈ Row44Top := by
    rw [row44_bindings.2.2.1]; exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hr : f reflection ∈ Row44Top := by
    rw [row44_bindings.2.2.2]; exact Subgroup.subset_closure (Set.mem_range_self 3)
  have hs : f s ∈ Row44Top := by
    have he : b⁻¹*reflection*b = s := by decide +kernel
    rw [← he,map_mul,map_mul,map_inv]
    exact Row44Top.mul_mem (Row44Top.mul_mem (Row44Top.inv_mem hb) hr) hb
  have hc : f c ∈ Row44Top := by
    have he : a*s = c := by decide +kernel
    rw [← he,map_mul]
    exact Row44Top.mul_mem ha hs
  apply literal_range allBlocks TernaryFourSignedAugmentation.scalar row44Generators
    ![inl (Multiplicative.ofAdd 1),inr a,inr b,inr reflection] _ ht
    (hom_mem_of_pair f Row44Top c s symmetric_generated hc hs)
  intro i
  fin_cases i
  · exact (action_inl _ _ _).trans row44_bindings.1
  · exact (action_inr _ _ _).trans row44_bindings.2.1
  · exact (action_inr _ _ _).trans row44_bindings.2.2.1
  · exact (action_inr _ _ _).trans row44_bindings.2.2.2

def row20Map := (MulEquiv.subgroupCongr row20_range).toMonoidHom.comp row20Action.rangeRestrict
def row43Map := (MulEquiv.subgroupCongr row43_range).toMonoidHom.comp row43Action.rangeRestrict
def row44Map := (MulEquiv.subgroupCongr row44_range).toMonoidHom.comp row44Action.rangeRestrict
def row45Map := (MulEquiv.subgroupCongr row45_range).toMonoidHom.comp row45Action.rangeRestrict
def row83Map := (MulEquiv.subgroupCongr row83_range).toMonoidHom.comp row83Action.rangeRestrict

theorem row20Map_surjective : Function.Surjective row20Map :=
  (MulEquiv.subgroupCongr row20_range).surjective.comp row20Action.rangeRestrict_surjective
theorem row43Map_surjective : Function.Surjective row43Map :=
  (MulEquiv.subgroupCongr row43_range).surjective.comp row43Action.rangeRestrict_surjective
theorem row44Map_surjective : Function.Surjective row44Map :=
  (MulEquiv.subgroupCongr row44_range).surjective.comp row44Action.rangeRestrict_surjective
theorem row45Map_surjective : Function.Surjective row45Map :=
  (MulEquiv.subgroupCongr row45_range).surjective.comp row45Action.rangeRestrict_surjective
theorem row83Map_surjective : Function.Surjective row83Map :=
  (MulEquiv.subgroupCongr row83_range).surjective.comp row83Action.rangeRestrict_surjective

theorem row20_quotientSocle (N : Subgroup Row20Top) [N.Normal] :
    SocleNormalGeneratorBound (Row20Top ⧸ N) 2 :=
  TernaryCentralComplementSocles.alternatingFour_product_socle_of_surjective
    (((QuotientGroup.mk' N).comp row20Map).comp productToModel)
    (((QuotientGroup.mk'_surjective N).comp row20Map_surjective).comp productToModel_surjective)

theorem row43_quotientSocle (N : Subgroup Row43Top) [N.Normal] :
    SocleNormalGeneratorBound (Row43Top ⧸ N) 1 :=
  TernaryScalarComplementSocles.alternating_dihedral_socle_of_surjective
    (((QuotientGroup.mk' N).comp row43Map).comp productDihedralToModel)
    (((QuotientGroup.mk'_surjective N).comp row43Map_surjective).comp
      productDihedralToModel_surjective)

theorem row44_quotientSocle (N : Subgroup Row44Top) [N.Normal] :
    SocleNormalGeneratorBound (Row44Top ⧸ N) 2 :=
  socle_two_of_normal_total TernaryFourSignedAugmentation.scalar
    NaturalFourNormalChains.symmetric_normal_total
    ((QuotientGroup.mk' N).comp row44Map)
    ((QuotientGroup.mk'_surjective N).comp row44Map_surjective)

theorem row45_quotientSocle (N : Subgroup Row45Top) [N.Normal] :
    SocleNormalGeneratorBound (Row45Top ⧸ N) 1 :=
  TernaryCentralComplementSocles.symmetricFour_product_socle_of_surjective
    (((QuotientGroup.mk' N).comp row45Map).comp productToModel)
    (((QuotientGroup.mk'_surjective N).comp row45Map_surjective).comp productToModel_surjective)

theorem row83_quotientSocle (N : Subgroup Row83Top) [N.Normal] :
    SocleNormalGeneratorBound (Row83Top ⧸ N) 2 :=
  TernaryScalarComplementSocles.symmetric_dihedral_socle_of_surjective
    (((QuotientGroup.mk' N).comp row83Map).comp productDihedralToModel)
    (((QuotientGroup.mk'_surjective N).comp row83Map_surjective).comp
      productDihedralToModel_surjective)

def row20_family : row20Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row20Interface.normalRegistry (fun N => by letI := N.2; exact row20_quotientSocle N.1)
def row43_family : row43Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row43Interface.normalRegistry (fun N => by letI := N.2; exact row43_quotientSocle N.1)
def row44_family : row44Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row44Interface.normalRegistry (fun N => by letI := N.2; exact row44_quotientSocle N.1)
def row45_family : row45Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row45Interface.normalRegistry (fun N => by letI := N.2; exact row45_quotientSocle N.1)
def row83_family : row83Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row83Interface.normalRegistry (fun N => by letI := N.2; exact row83_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles

end
