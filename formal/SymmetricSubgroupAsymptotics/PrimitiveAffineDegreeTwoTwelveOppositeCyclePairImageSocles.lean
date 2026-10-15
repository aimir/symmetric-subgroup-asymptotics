import SymmetricSubgroupAsymptotics.SixPairOppositeCycleSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Four original pair images share the cycle-plus-opposite-transposition
structure. Two charts merely relabel the six original physical pairs.
Socle capacity two is exact for89,91,143 and alternate for60. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairOppositeCycleSocles

def tripleCodes : Fin 3 → Model := ![1,cycleModel,oppositeModel]
def quartetCodes : Fin 4 → Model := ![1,1,cycleModel,oppositeModel]

def relabel89 : Equiv.Perm (Fin 6) where
  toFun := ![5,0,3,4,1,2]
  invFun := ![1,4,5,2,3,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def relabel91 : Equiv.Perm (Fin 6) where
  toFun := ![0,3,4,1,2,5]
  invFun := ![0,3,4,1,2,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def chart89 : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr relabel89 (Equiv.refl (ZMod 2))).trans SixPairCyclicSymmetricSocles.pointChart

def chart91 : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr relabel91 (Equiv.refl (ZMod 2))).trans SixPairCyclicSymmetricSocles.pointChart

theorem row60_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row60Generators i) (literalAction (tripleCodes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row89_preserves : ∀ i,
    BinaryPairFrame.Preserves chart89 (row89Generators i) (literalAction (tripleCodes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row91_preserves : ∀ i,
    BinaryPairFrame.Preserves chart91 (row91Generators i) (literalAction (tripleCodes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row143_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row143Generators i) (literalAction (quartetCodes i)) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row60AtTwo_quotientSocle (N : Subgroup Row60Top) [N.Normal] :
    SocleNormalGeneratorBound (Row60Top ⧸ N) 2 :=
  quotientSocle_of_generators SixPairCyclicSymmetricSocles.pointChart row60Generators tripleCodes
    1 2 cycleModel_action oppositeModel_action row60_preserves N

theorem row89_quotientSocle (N : Subgroup Row89Top) [N.Normal] :
    SocleNormalGeneratorBound (Row89Top ⧸ N) 2 :=
  quotientSocle_of_generators chart89 row89Generators tripleCodes
    1 2 cycleModel_action oppositeModel_action row89_preserves N

theorem row91_quotientSocle (N : Subgroup Row91Top) [N.Normal] :
    SocleNormalGeneratorBound (Row91Top ⧸ N) 2 :=
  quotientSocle_of_generators chart91 row91Generators tripleCodes
    1 2 cycleModel_action oppositeModel_action row91_preserves N

theorem row143_quotientSocle (N : Subgroup Row143Top) [N.Normal] :
    SocleNormalGeneratorBound (Row143Top ⧸ N) 2 :=
  quotientSocle_of_generators SixPairCyclicSymmetricSocles.pointChart row143Generators quartetCodes
    2 3 cycleModel_action oppositeModel_action row143_preserves N

def row60AtTwo_family : row60Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row60AtTwo_quotientSocle N.1)

def row89_family : row89Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row89_quotientSocle N.1)

def row91_family : row91Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row91_quotientSocle N.1)

def row143_family : row143Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row143_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles

end
