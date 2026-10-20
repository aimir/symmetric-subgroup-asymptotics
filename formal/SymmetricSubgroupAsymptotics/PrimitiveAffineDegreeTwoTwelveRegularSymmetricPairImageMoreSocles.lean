import SymmetricSubgroupAsymptotics.SixPairRegularSymmetricSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Two further original actions have the same regular S3 pair image.
Both conclusions match the exact historical socle capacity two. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageMoreSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairRegularSymmetricSocles

def row3Codes : Fin 3 → DihedralGroup 3 := ![.r 1,.sr 0,1]
def row106Codes : Fin 5 → DihedralGroup 3 := ![1,1,1,.r 1,.sr 0]

theorem row3_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row3Generators i) (dihedralMap (row3Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row106_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row106Generators i) (dihedralMap (row106Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row3_quotientSocle (N : Subgroup Row3Top) [N.Normal] :
    SocleNormalGeneratorBound (Row3Top ⧸ N) 2 :=
  quotientSocle_of_generators row3Generators row3Codes 0 1 rfl rfl row3_preserves N

theorem row106_quotientSocle (N : Subgroup Row106Top) [N.Normal] :
    SocleNormalGeneratorBound (Row106Top ⧸ N) 2 :=
  quotientSocle_of_generators row106Generators row106Codes 3 4 rfl rfl row106_preserves N

def row3_family : row3Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row3_quotientSocle N.1)

def row106_family : row106Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row106_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageMoreSocles

end
