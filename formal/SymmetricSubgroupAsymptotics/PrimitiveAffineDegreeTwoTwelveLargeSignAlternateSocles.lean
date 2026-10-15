import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveBinarySignSocles

/-! The full-sign A4 and even-sign S4 actions admit capacity two. These
are alternate bounds on the exact literal tops, with their original
quotient maps, rather than historical capacity-one assertions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLargeSignAlternateSocles

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open TernaryFourBlockPermutationGenerators FourBlockBinarySignGeneration
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row280_bindings (i : Fin 4) :
    AlternatingBinarySignGeneration.action false (AlternatingBinarySignGeneration.lifts false i) =
      row280Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row280_range : (AlternatingBinarySignGeneration.action false).range = Row280Top :=
  AlternatingBinarySignGeneration.range_eq false _ row280_bindings

def row280Map : AlternatingBinarySignGeneration.Model false →* Row280Top :=
  (MulEquiv.subgroupCongr row280_range).toMonoidHom.comp
    (AlternatingBinarySignGeneration.action false).rangeRestrict

theorem row280Map_surjective : Function.Surjective row280Map :=
  (MulEquiv.subgroupCongr row280_range).surjective.comp
    (AlternatingBinarySignGeneration.action false).rangeRestrict_surjective

abbrev EvenSymmetricModel :=
  FourBlockBinarySignGeneration.AffineModel (R := Equiv.Perm (Fin 4)) true
abbrev evenSymmetricAction :=
  BinarySignTernaryPointAction.action (space (R := Equiv.Perm (Fin 4)) true)

def row281Lifts : Fin 4 → EvenSymmetricModel :=
  ![inl (Multiplicative.ofAdd (Pi.single 0 1)),
    inr (inl (Multiplicative.ofAdd (signSeed true))),
    inr (inr c),inr (inr (Equiv.swap 1 2))]

theorem row281_bindings (i : Fin 4) : evenSymmetricAction (row281Lifts i) = row281Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row281_range : evenSymmetricAction.range = Row281Top := by
  have hm (i : Fin 4) : evenSymmetricAction (row281Lifts i) ∈ Row281Top := by
    rw [row281_bindings]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply action_range_eq true c (fun _ => rfl) row281Generators row281Lifts
    row281_bindings (hm 0) (hm 1) (hm 2)
  · intro K hc hg
    have hs : s ∈ K := by
      have he : c * Equiv.swap 1 2 * c⁻¹ = s := by decide +kernel
      rw [← he]
      exact K.mul_mem (K.mul_mem hc (hg 3)) (K.inv_mem hc)
    exact top_unique (fun g _ => symmetric_mem K hc hs g)
  · intro i
    fin_cases i
    · change evenSymmetricAction 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · change evenSymmetricAction 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · exact hm 2
    · exact hm 3

def row281Map : EvenSymmetricModel →* Row281Top :=
  (MulEquiv.subgroupCongr row281_range).toMonoidHom.comp evenSymmetricAction.rangeRestrict

theorem row281Map_surjective : Function.Surjective row281Map :=
  (MulEquiv.subgroupCongr row281_range).surjective.comp evenSymmetricAction.rangeRestrict_surjective

theorem row280AtTwo_quotientSocle (N : Subgroup Row280Top) [N.Normal] :
    SocleNormalGeneratorBound (Row280Top ⧸ N) 2 :=
  UniformBinarySignTernarySocles.socle_of_irreducible (space false)
    (UniformBinarySignTernarySocles.irreducible_transitive (space false)
      AlternatingBinarySignGeneration.transitive (pair_mem false 0 1) (pair_mem false 0 2))
    1 1 (by decide) UniformBinarySignTernarySocles.alternating_uniform
    PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles.alternating_normalGen
    ((QuotientGroup.mk' N).comp row280Map)
    ((QuotientGroup.mk'_surjective N).comp row280Map_surjective)

theorem row281AtTwo_quotientSocle (N : Subgroup Row281Top) [N.Normal] :
    SocleNormalGeneratorBound (Row281Top ⧸ N) 2 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space true)
    c symmetric_orbit (pair_mem true 0 1) (pair_mem true 0 2)
    1 symmetric_normalGen ((QuotientGroup.mk' N).comp row281Map)
    ((QuotientGroup.mk'_surjective N).comp row281Map_surjective)

def row280AtTwo_family : row280Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row280Interface.normalRegistry (fun N => by letI := N.2; exact row280AtTwo_quotientSocle N.1)
def row281AtTwo_family : row281Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row281Interface.normalRegistry (fun N => by letI := N.2; exact row281AtTwo_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLargeSignAlternateSocles

end
