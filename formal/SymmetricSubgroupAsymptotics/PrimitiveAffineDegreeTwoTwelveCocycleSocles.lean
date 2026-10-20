import SymmetricSubgroupAsymptotics.TernaryFourPairingCocycles
import SymmetricSubgroupAsymptotics.AffineIrreducibleRangeGeneration
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Exact cocycle images for the original rows4,132,177. Every quotient
uses the original top and its original normal subgroup. The complement
offsets are retained in the displayed maps, and the affine range proofs
use actual lifts rather than assuming pure block generators belong. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCocycleSocles

open SemidirectProduct TernaryFourAugmentationRepresentation
open TernaryFourCocycleImages TernaryFourPairingCocycles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev row4Action := complementAction alternatingBlocks 1 alternating
abbrev row132Action := action alternatingBlocks 1 alternating
abbrev row177Action := action symmetricBlocks TernaryFourSignedAugmentation.scalar symmetric
abbrev AlternatingModel := TernaryFourScalarAugmentation.Model alternatingBlocks 1
abbrev SymmetricModel := TernaryFourScalarAugmentation.Model symmetricBlocks TernaryFourSignedAugmentation.scalar

def seed : Vector := ![1,1,1]

theorem seed_ne_zero : seed ≠ 0 := by decide +kernel

def row132Lifts : Fin 4 → AlternatingModel :=
  ![inl (Multiplicative.ofAdd seed),inr kleinFirst,inr kleinSecond,
    ⟨Multiplicative.ofAdd ![0,2,2],alternatingSecond⟩]

def row177Lifts : Fin 4 → SymmetricModel :=
  ![inl (Multiplicative.ofAdd seed),inr kleinFirst.1,
    ⟨Multiplicative.ofAdd ![1,1,0],Equiv.swap 0 1⟩,
    ⟨Multiplicative.ofAdd ![1,1,1],Equiv.swap 1 2⟩]

theorem row4_bindings : row4Action alternatingFirst = row4Generators 0 ∧
    row4Action alternatingSecond = row4Generators 1 := by
  constructor <;> apply Equiv.ext <;> intro i <;> revert i <;> decide +kernel

theorem row132_bindings (i : Fin 4) : row132Action (row132Lifts i) = row132Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row177_bindings (i : Fin 4) : row177Action (row177Lifts i) = row177Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row4_range : row4Action.range = Row4Top := by
  let T := Row4Top
  have hmem (g : A4) : row4Action g ∈ T := by
    have hg : g ∈ Subgroup.closure ({alternatingFirst,alternatingSecond} : Set A4) := by
      rw [alternating_pair_generated]
      exact Subgroup.mem_top _
    induction hg using Subgroup.closure_induction with
    | mem h hh =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · rw [row4_bindings.1]
        exact Subgroup.subset_closure (Set.mem_range_self 0)
      · rw [row4_bindings.2]
        exact Subgroup.subset_closure (Set.mem_range_self 1)
    | one => simpa only [map_one] using T.one_mem
    | mul g h _ _ hg hh => simpa only [map_mul] using T.mul_mem hg hh
    | inv g _ hg => simpa only [map_inv] using T.inv_mem hg
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    exact hmem g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨alternatingFirst,row4_bindings.1⟩
    · exact ⟨alternatingSecond,row4_bindings.2⟩

theorem alternating_irreducible :
    AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup alternatingBlocks 1) :=
  TernaryFourScalarAugmentation.irreducible_of_even_lifts alternatingBlocks 1
    (fun g => ⟨g,rfl,rfl⟩)

theorem symmetric_irreducible :
    AffineModel.Irreducible (TernaryFourScalarAugmentation.linearGroup
      symmetricBlocks TernaryFourSignedAugmentation.scalar) :=
  TernaryFourScalarAugmentation.irreducible_of_even_lifts
    symmetricBlocks TernaryFourSignedAugmentation.scalar
    (fun g => ⟨g.1,rfl,TernaryFourSignedAugmentation.scalar_even g.1 g.2⟩)

theorem row132_right_generated :
    Subgroup.closure (Set.range (fun i => (row132Lifts i).right)) = ⊤ := by
  apply alternating_of_klein_cycle
  · exact Subgroup.subset_closure (Set.mem_range.mpr ⟨1,rfl⟩)
  · exact Subgroup.subset_closure (Set.mem_range.mpr ⟨3,rfl⟩)

theorem row177_right_generated :
    Subgroup.closure (Set.range (fun i => (row177Lifts i).right)) = ⊤ := by
  apply symmetric_of_klein_swaps
  · exact Subgroup.subset_closure (Set.mem_range.mpr ⟨1,rfl⟩)
  · exact Subgroup.subset_closure (Set.mem_range.mpr ⟨2,rfl⟩)
  · exact Subgroup.subset_closure (Set.mem_range.mpr ⟨3,rfl⟩)

theorem row132_range : row132Action.range = Row132Top := by
  apply AffineIrreducibleRangeGeneration.range_eq_closure_of_lifts alternatingBlocks 1
    alternating_irreducible row132Action row132Generators row132Lifts row132_bindings
    row132_right_generated seed seed_ne_zero
  change row132Action (row132Lifts 0) ∈ Row132Top
  rw [row132_bindings]
  exact Subgroup.subset_closure (Set.mem_range_self 0)

theorem row177_range : row177Action.range = Row177Top := by
  apply AffineIrreducibleRangeGeneration.range_eq_closure_of_lifts
    symmetricBlocks TernaryFourSignedAugmentation.scalar symmetric_irreducible
    row177Action row177Generators row177Lifts row177_bindings
    row177_right_generated seed seed_ne_zero
  change row177Action (row177Lifts 0) ∈ Row177Top
  rw [row177_bindings]
  exact Subgroup.subset_closure (Set.mem_range_self 0)

def row4Map : A4 →* Row4Top :=
  (MulEquiv.subgroupCongr row4_range).toMonoidHom.comp row4Action.rangeRestrict

def row132Map : AlternatingModel →* Row132Top :=
  (MulEquiv.subgroupCongr row132_range).toMonoidHom.comp row132Action.rangeRestrict

def row177Map : SymmetricModel →* Row177Top :=
  (MulEquiv.subgroupCongr row177_range).toMonoidHom.comp row177Action.rangeRestrict

theorem row4Map_surjective : Function.Surjective row4Map :=
  (MulEquiv.subgroupCongr row4_range).surjective.comp row4Action.rangeRestrict_surjective

theorem row132Map_surjective : Function.Surjective row132Map :=
  (MulEquiv.subgroupCongr row132_range).surjective.comp row132Action.rangeRestrict_surjective

theorem row177Map_surjective : Function.Surjective row177Map :=
  (MulEquiv.subgroupCongr row177_range).surjective.comp row177Action.rangeRestrict_surjective

theorem row4_quotientSocle (N : Subgroup Row4Top) [N.Normal] :
    SocleNormalGeneratorBound (Row4Top ⧸ N) 1 :=
  socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective ((QuotientGroup.mk' N).comp row4Map)
      ((QuotientGroup.mk'_surjective N).comp row4Map_surjective)
      NaturalFourNormalChains.alternating_normal_total)

theorem row132_quotientSocle (N : Subgroup Row132Top) [N.Normal] :
    SocleNormalGeneratorBound (Row132Top ⧸ N) 1 := by
  apply TernaryFourScalarAugmentation.socle_of_surjective alternatingBlocks 1
    (fun g h he => Subtype.ext (congrArg Prod.snd he)) alternating_irreducible
    seed seed_ne_zero (by decide) _ ((QuotientGroup.mk' N).comp row132Map)
    ((QuotientGroup.mk'_surjective N).comp row132Map_surjective)
  intro M hM
  letI := hM
  exact socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective (QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M) NaturalFourNormalChains.alternating_normal_total)

theorem row177_quotientSocle (N : Subgroup Row177Top) [N.Normal] :
    SocleNormalGeneratorBound (Row177Top ⧸ N) 1 := by
  apply TernaryFourScalarAugmentation.socle_of_surjective
    symmetricBlocks TernaryFourSignedAugmentation.scalar
    (fun g h he => congrArg Prod.snd he) symmetric_irreducible
    seed seed_ne_zero (by decide) _ ((QuotientGroup.mk' N).comp row177Map)
    ((QuotientGroup.mk'_surjective N).comp row177Map_surjective)
  intro M hM
  letI := hM
  exact socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective (QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M) NaturalFourNormalChains.symmetric_normal_total)

def row4_family : row4Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row4Interface.normalRegistry (fun N => by letI := N.2; exact row4_quotientSocle N.1)

def row132_family : row132Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row132Interface.normalRegistry (fun N => by letI := N.2; exact row132_quotientSocle N.1)

def row177_family : row177Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row177Interface.normalRegistry (fun N => by letI := N.2; exact row177_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCocycleSocles

end
