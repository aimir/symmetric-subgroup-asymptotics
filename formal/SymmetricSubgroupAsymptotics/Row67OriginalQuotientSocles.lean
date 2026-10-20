import SymmetricSubgroupAsymptotics.Row67OriginalKernelChart
import SymmetricSubgroupAsymptotics.OriginalFixedFreeMonolithSingletonSocles
import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row67OriginalQuotientSocles
open Row67OriginalQuartetFrame Row67OriginalKernelChart
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
 theorem quotientSocle (N : Subgroup Row67Top) [N.Normal] :
    SocleNormalGeneratorBound (Row67Top ⧸ N) 1 := by
  let O := alternatingGroup (Fin 3)
  have hc : Nat.card O=3 := by
    change Nat.card (alternatingGroup (Fin 3))=3
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  letI : NeZero (Nat.card O : ZMod 2) := ⟨by rw [hc]; decide⟩
  exact OriginalFixedFreeMonolithSingletonSocles.quotientSocle frame.top top_surjective R chart
    BinarySymmetricThreeAugmentation.uniform_one O
    NaturalThreeNormalClassification.alternating_le_nontrivial_normal
    BinarySymmetricThreeAugmentation.fixed_free
    (normal_generating_singletons_of_finite_normal_total
      NaturalFourNormalChains.symmetric_three_normal_total) N
end SymmetricSubgroupAsymptotics.Row67OriginalQuotientSocles
