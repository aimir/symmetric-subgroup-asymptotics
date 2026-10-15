import SymmetricSubgroupAsymptotics.UniformBinarySignTernarySocles
import SymmetricSubgroupAsymptotics.AlternatingBinarySignGeneration
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! The original even-sign alternating row is a literal instance of the
uniform-sign template. Its stored bound is two. The full-sign alternating
row at stored bound one requires a stronger sharing theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles

open BinarySignTernaryLinear FourBlockBinarySignSpaces
open AlternatingBinarySignGeneration TernaryFourPairingCocycles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row271_bindings (i : Fin 4) : action true (lifts true i) = row271Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row271_range : (action true).range = Row271Top := range_eq true _ row271_bindings

def row271Map : Model true →* Row271Top :=
  (MulEquiv.subgroupCongr row271_range).toMonoidHom.comp (action true).rangeRestrict

theorem row271Map_surjective : Function.Surjective row271Map :=
  (MulEquiv.subgroupCongr row271_range).surjective.comp (action true).rangeRestrict_surjective

theorem alternating_normalGen (K : Subgroup A4) (hK : K.Normal) : MarkedC4.normalGen K ≤ 1 := by
  letI := hK
  obtain ⟨g,hg⟩ := normal_generating_singletons_of_finite_normal_total
    NaturalFourNormalChains.alternating_normal_total K hK
  exact normalGen_le_of_fin_tuple g hg

theorem row271_quotientSocle (N : Subgroup Row271Top) [N.Normal] :
    SocleNormalGeneratorBound (Row271Top ⧸ N) 2 :=
  UniformBinarySignTernarySocles.socle_of_irreducible (space true)
    (UniformBinarySignTernarySocles.irreducible_transitive (space true) transitive
      (pair_mem true 0 1) (pair_mem true 0 2))
    1 1 (by decide) UniformBinarySignTernarySocles.alternating_uniform alternating_normalGen
    ((QuotientGroup.mk' N).comp row271Map)
    ((QuotientGroup.mk'_surjective N).comp row271Map_surjective)

def row271_family : row271Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row271Interface.normalRegistry (fun N => by letI := N.2; exact row271_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles

end
