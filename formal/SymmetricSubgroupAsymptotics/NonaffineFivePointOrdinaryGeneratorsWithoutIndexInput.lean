import SymmetricSubgroupAsymptotics.S5SubgroupProjectiveClassification
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixFiveDivisibility
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
import SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators

/-! An actual nonaffine five-point subgroup is nonsoluble, hence contains
A5 by the internally proved Burnside theorem. No simple-index packet,
Tracey input, or CFSG model distinction is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineFivePointOrdinaryGeneratorsWithoutIndexInput
open PrimitiveSocleRawStructure

theorem genRank_le_two (J : Subgroup (Equiv.Perm (Fin 5)))
    (D : NonaffineData J (Fin 5)) : MarkedC4.genRank J ≤ 2 := by
  rcases S5SubgroupProjectiveClassification.eq_alternating_or_top_of_not_isSolvable
    burnsideTwoPrimeSolvability J D.not_isSolvable with hA | htop
  · rw [hA]
    exact CFSGAlternatingGeneration.genRank_le_two 5 (by decide)
  · let e : J ≃* Equiv.Perm (Fin 5) :=
      (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv)
    exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans
      (NaturalDegreeFiveSocleOrdinaryGenerators.symmetric_genRank_le_two 5 (by decide))

end SymmetricSubgroupAsymptotics.NonaffineFivePointOrdinaryGeneratorsWithoutIndexInput
