import SymmetricSubgroupAsymptotics.SecondPairChartSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Original row148, zero-based index147, is a selected literal pilot
for the common second-pair-chart theorem. Capacity three is an explicit
alternate profile; its historical capacity and natural capacity are
unchanged. Only the three original generators on twelve points are
checked here. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartPilot

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue SecondPairChartSocles

def row148Codes : Fin 3 → Fin 5 := ![3,1,2]

theorem row148_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row148Generators i) (pairImage (row148Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row148AtThree_quotientSocle (N : Subgroup Row148Top) [N.Normal] :
    SocleNormalGeneratorBound (Row148Top ⧸ N) 3 :=
  quotientSocle_of_codes row148Generators row148Codes row148_preserves 0 1
    (Or.inl rfl) rfl (Or.inl ⟨2,rfl⟩) N

def row148AtThree_family : row148Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row148AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartPilot

end
