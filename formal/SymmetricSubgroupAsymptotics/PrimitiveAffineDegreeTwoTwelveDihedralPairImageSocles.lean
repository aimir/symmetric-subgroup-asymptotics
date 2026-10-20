import SymmetricSubgroupAsymptotics.SixPairDihedralSocles
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Two original twelve-point actions share the same six-pair dihedral
image. Capacity three is exact for row193. The row145 capacity-three
bound is an explicit alternate profile, separate from its historical two.
Both original natural-module capacities remain one. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDihedralPairImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairCyclicSymmetricSocles SixPairDihedralSocles

theorem row145_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row145Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row193_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row193Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row145Frame : BinaryPairFrame Row145Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row145Generators tops row145_preserves

def row193Frame : BinaryPairFrame Row193Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row193Generators tops row193_preserves

theorem row145AtThree_quotientSocle (N : Subgroup Row145Top) [N.Normal] :
    SocleNormalGeneratorBound (Row145Top ⧸ N) 3 := by
  apply SixPairDihedralSocles.quotientSocle row145Frame
    (closureGenerators row145Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row145Generators tops row145_preserves 1) ?_ N
  exact (BinaryPairFrame.ofGenerators_top_range pointChart row145Generators tops row145_preserves).trans
    dihedralMap_range.symm

theorem row193_quotientSocle (N : Subgroup Row193Top) [N.Normal] :
    SocleNormalGeneratorBound (Row193Top ⧸ N) 3 := by
  apply SixPairDihedralSocles.quotientSocle row193Frame
    (closureGenerators row193Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row193Generators tops row193_preserves 1) ?_ N
  exact (BinaryPairFrame.ofGenerators_top_range pointChart row193Generators tops row193_preserves).trans
    dihedralMap_range.symm

def row145AtThree_family : row145Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row145AtThree_quotientSocle N.1)

def row193_family : row193Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row193_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDihedralPairImageSocles

end
