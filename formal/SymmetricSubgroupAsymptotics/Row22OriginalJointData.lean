import SymmetricSubgroupAsymptotics.Row22ActualModelMap
import SymmetricSubgroupAsymptotics.NormalChainCyclicProductGenerators
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row22OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def naturalWitness : LiteralCyclicOrbitWitness Row22Top 2 where
  element := closureGenerators row22Generators 0 * closureGenerators row22Generators 1 *
    closureGenerators row22Generators 2
  representative := ![0,1]
  orbitIndex := ![0,1,0,0,0,1,1,1,0,0,1,1]
  exponent := ![0,0,1,5,4,4,3,1,3,2,5,2]
  point_eq := by decide +kernel

theorem quotientSocle (N : Subgroup Row22Top) [N.Normal] :
    SocleNormalGeneratorBound (Row22Top ⧸ N) 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic Row22DirectedEdgeModel.Bit := isCyclic_of_prime_card (p := 2) (by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2)
  have hmodel := normal_pairs_of_normal_chain_cyclic_product
    (C := Row22DirectedEdgeModel.Bit) NaturalFourNormalChains.symmetric_normal_total
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_of_surjective Row22DirectedEdgeModel.originalMap
      Row22DirectedEdgeModel.originalMap_surjective hmodel) N

def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row22Interface 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)
  natural := naturalWitness.uniform _
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row22Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row22OriginalJointData
