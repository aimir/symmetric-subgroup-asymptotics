import SymmetricSubgroupAsymptotics.SecondPairChartCyclicImageSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Original joint twelve-point actions in the shared second physical pair
chart. Each literal certificate checks only its original generator images.
The generic structural theorem retains both actual kernels and images.
Historical profiles remain unchanged for alternate capacity-three exports. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue SecondPairChartSocles

/-- Original row51, zero-based index50, joint branch; historical (2,1). -/
def row51Codes : Fin 4 → Fin 5 := ![0,4,0,1]

theorem row51_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row51Generators i) (pairImage (row51Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row51_quotientSocle (N : Subgroup Row51Top) [N.Normal] :
    SocleNormalGeneratorBound (Row51Top ⧸ N) 2 :=
  SecondPairChartCyclicImageSocles.cyclic_quotientSocle_of_codes
    row51Generators row51Codes row51_preserves 1 3 rfl rfl
    (by decide +kernel) N

def row51_family : row51Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row51_quotientSocle N.1)

/-- Original row141, zero-based index140, joint branch; historical (2,1). -/
def row141Codes : Fin 3 → Fin 5 := ![3,0,1]

theorem row141_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row141Generators i) (pairImage (row141Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row141_quotientSocle (N : Subgroup Row141Top) [N.Normal] :
    SocleNormalGeneratorBound (Row141Top ⧸ N) 2 :=
  SecondPairChartCyclicImageSocles.wreath_quotientSocle_of_codes
    row141Generators row141Codes row141_preserves 0 2 rfl rfl
    (by decide +kernel) N

def row141_family : row141Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row141_quotientSocle N.1)

/-- Original row142, zero-based index141, joint branch; historical (2,1). -/
def row142Codes : Fin 4 → Fin 5 := ![3,0,0,1]

theorem row142_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row142Generators i) (pairImage (row142Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row142_quotientSocle (N : Subgroup Row142Top) [N.Normal] :
    SocleNormalGeneratorBound (Row142Top ⧸ N) 2 :=
  SecondPairChartCyclicImageSocles.wreath_quotientSocle_of_codes
    row142Generators row142Codes row142_preserves 0 3 rfl rfl
    (by decide +kernel) N

def row142_family : row142Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row142_quotientSocle N.1)

/-- Original row189, zero-based index188, joint branch; historical (2,1). -/
def row189Codes : Fin 3 → Fin 5 := ![3,0,1]

theorem row189_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row189Generators i) (pairImage (row189Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row189_quotientSocle (N : Subgroup Row189Top) [N.Normal] :
    SocleNormalGeneratorBound (Row189Top ⧸ N) 2 :=
  SecondPairChartCyclicImageSocles.wreath_quotientSocle_of_codes
    row189Generators row189Codes row189_preserves 0 2 rfl rfl
    (by decide +kernel) N

def row189_family : row189Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row189_quotientSocle N.1)

/-- Original row222, zero-based index221, joint branch; historical (2,1). -/
def row222Codes : Fin 3 → Fin 5 := ![3,0,1]

theorem row222_preserves : ∀ i,
    BinaryPairFrame.Preserves outerFrame (row222Generators i) (pairImage (row222Codes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row222_quotientSocle (N : Subgroup Row222Top) [N.Normal] :
    SocleNormalGeneratorBound (Row222Top ⧸ N) 2 :=
  SecondPairChartCyclicImageSocles.wreath_quotientSocle_of_codes
    row222Generators row222Codes row222_preserves 0 2 rfl rfl
    (by decide +kernel) N

def row222_family : row222Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row222_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles

end
