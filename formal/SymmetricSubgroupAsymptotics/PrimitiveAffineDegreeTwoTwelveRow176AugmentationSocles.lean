import SymmetricSubgroupAsymptotics.TernaryFourScalarAugmentation
import SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationSocles

/-! Exact row176 is the augmentation module acted on by literal A4 × C2.
The central involution negates the ternary coordinates. Its complement
uses the proved cyclic-image/normal-axis theorem; no normal-chain claim
for the direct product is made. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow176AugmentationSocles

open TernaryFourAugmentationRepresentation SemidirectProduct
open TernaryFourBlockPermutationGenerators
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev A4 := AlternatingFourCentralTwoSocles.A4
abbrev C2 := AlternatingFourCentralTwoSocles.C2
abbrev Complement := AlternatingFourCentralTwoSocles.Model
abbrev Top := Row176Top
abbrev seed := PrimitiveAffineDegreeTwoTwelveAugmentationSocles.seed

def bitScalar : C2 →* (ZMod 3)ˣ where
  toFun z := (-1) ^ z.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def blocks : Complement →* Equiv.Perm (Fin 4) :=
  (alternatingGroup (Fin 4)).subtype.comp (MonoidHom.fst A4 C2)

def scalars : Complement →* (ZMod 3)ˣ := bitScalar.comp (MonoidHom.snd A4 C2)

theorem separating : Function.Injective (fun g : Complement => (scalars g,blocks g)) := by
  intro g h hgh
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.snd hgh
  · have hi : Function.Injective bitScalar := by decide +kernel
    apply hi
    exact congrArg Prod.fst hgh

theorem irreducible :
    AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup blocks scalars) := by
  apply TernaryFourScalarAugmentation.irreducible_of_even_lifts
  intro g
  exact ⟨(g,1),rfl,rfl⟩

abbrev Model := TernaryFourScalarAugmentation.Model blocks scalars
abbrev blockPerm := TernaryFourScalarAugmentation.blockPerm blocks scalars
abbrev action := TernaryFourScalarAugmentation.action blocks scalars

def first : Complement := (⟨a,a_even⟩,1)
def second : Complement := (⟨b,b_even⟩,1)
def negative : Complement := (1,Multiplicative.ofAdd 1)

theorem translation_binding :
    TernaryFourAugmentationAffineImage.translationPerm (Multiplicative.ofAdd seed) =
      row176Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem negative_binding : blockPerm negative = row176Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem first_binding : blockPerm first = row176Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem second_binding : blockPerm second = row176Generators 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem even_mem (g : A4) : blockPerm (g,1) ∈ Top := by
  let H : Subgroup A4 := Top.comap
    (blockPerm.comp (MonoidHom.inl A4 C2))
  have hA : alternatingGroup (Fin 4) ≤ H.map (alternatingGroup (Fin 4)).subtype := by
    conv_lhs => rw [← alternating_generated]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨⟨a,a_even⟩,?_,rfl⟩
      change blockPerm first ∈ Top
      rw [first_binding]
      exact Subgroup.subset_closure (Set.mem_range_self 2)
    · refine ⟨⟨b,b_even⟩,?_,rfl⟩
      change blockPerm second ∈ Top
      rw [second_binding]
      exact Subgroup.subset_closure (Set.mem_range_self 3)
  obtain ⟨x,hx,hxg⟩ := hA g.2
  have he : x = g := Subtype.ext hxg
  subst x
  exact hx

theorem central_mem (z : C2) : blockPerm (1,z) ∈ Top := by
  have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 := by
    exact (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) z
  rcases hz with rfl | rfl
  · change blockPerm 1 ∈ Top
    rw [map_one]
    exact Top.one_mem
  · change blockPerm negative ∈ Top
    rw [negative_binding]
    exact Subgroup.subset_closure (Set.mem_range_self 1)

theorem complement_mem (g : Complement) : blockPerm g ∈ Top := by
  have he : g = (g.1,1) * (1,g.2) := by ext <;> simp
  rw [he,map_mul]
  exact Top.mul_mem (even_mem g.1) (central_mem g.2)

theorem translation_mem (v : Multiplicative Vector) :
    TernaryFourAugmentationAffineImage.translationPerm v ∈ Top :=
  TernaryFourScalarAugmentation.translation_mem_of_irreducible blocks scalars
    irreducible Top complement_mem seed
    PrimitiveAffineDegreeTwoTwelveAugmentationSocles.seed_ne_zero
    (by rw [translation_binding]; exact Subgroup.subset_closure (Set.mem_range_self 0)) v

theorem literal_range : action.range = Top := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    rw [← inl_left_mul_inr_right g,map_mul,
      TernaryFourScalarAugmentation.action_inl,TernaryFourScalarAugmentation.action_inr]
    exact Top.mul_mem (translation_mem g.left) (complement_mem g.right)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨inl (Multiplicative.ofAdd seed),
        (TernaryFourScalarAugmentation.action_inl blocks scalars _).trans translation_binding⟩
    · exact ⟨inr negative,
        (TernaryFourScalarAugmentation.action_inr blocks scalars _).trans negative_binding⟩
    · exact ⟨inr first,
        (TernaryFourScalarAugmentation.action_inr blocks scalars _).trans first_binding⟩
    · exact ⟨inr second,
        (TernaryFourScalarAugmentation.action_inr blocks scalars _).trans second_binding⟩

def modelToTop : Model →* Top :=
  (MulEquiv.subgroupCongr literal_range).toMonoidHom.comp action.rangeRestrict

theorem modelToTop_surjective : Function.Surjective modelToTop :=
  (MulEquiv.subgroupCongr literal_range).surjective.comp action.rangeRestrict_surjective

theorem quotientSocle (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 1 := by
  apply TernaryFourScalarAugmentation.socle_of_surjective blocks scalars separating
    irreducible seed PrimitiveAffineDegreeTwoTwelveAugmentationSocles.seed_ne_zero (by decide)
    _ ((QuotientGroup.mk' N).comp modelToTop)
    ((QuotientGroup.mk'_surjective N).comp modelToTop_surjective)
  intro M hM
  letI := hM
  exact AlternatingFourCentralTwoSocles.quotientSocle M

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 1 := by
  letI := N.2
  exact quotientSocle N.1

noncomputable def family : row176Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row176Interface.normalRegistry topSocle

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow176AugmentationSocles

end
