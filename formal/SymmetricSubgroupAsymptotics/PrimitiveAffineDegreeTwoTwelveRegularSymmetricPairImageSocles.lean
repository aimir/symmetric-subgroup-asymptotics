import SymmetricSubgroupAsymptotics.SixPairRegularSymmetricSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Three original twelve-point actions have the same regular S3 pair
image. Capacity two is exact for row135. The row69 and row107 conclusions
are alternate capacities, separate from their historical capacity one. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairRegularSymmetricSocles

def row69Codes : Fin 4 → DihedralGroup 3 := ![1, 1, .r 1, .sr 0]
def row107Codes : Fin 5 → DihedralGroup 3 := ![1, 1, 1, .r 1, .sr 0]
def row135Codes : Fin 3 → DihedralGroup 3 := ![1, .r 1, .sr 0]

theorem row69_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row69Generators i) (dihedralMap (row69Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row107_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row107Generators i) (dihedralMap (row107Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row135_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row135Generators i) (dihedralMap (row135Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row69AtTwo_quotientSocle (N : Subgroup Row69Top) [N.Normal] :
    SocleNormalGeneratorBound (Row69Top ⧸ N) 2 :=
  quotientSocle_of_generators row69Generators row69Codes 2 3 rfl rfl row69_preserves N

theorem row107AtTwo_quotientSocle (N : Subgroup Row107Top) [N.Normal] :
    SocleNormalGeneratorBound (Row107Top ⧸ N) 2 :=
  quotientSocle_of_generators row107Generators row107Codes 3 4 rfl rfl row107_preserves N

theorem row135_quotientSocle (N : Subgroup Row135Top) [N.Normal] :
    SocleNormalGeneratorBound (Row135Top ⧸ N) 2 :=
  quotientSocle_of_generators row135Generators row135Codes 1 2 rfl rfl row135_preserves N

def row69AtTwo_family : row69Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row69AtTwo_quotientSocle N.1)

def row107AtTwo_family : row107Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row107AtTwo_quotientSocle N.1)

def row135_family : row135Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row135_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles

end
