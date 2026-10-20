import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerCoupledHeads

/-! Catalogue adapter for the independently checked row-one coupled table.
The table is compiled separately so changes to other catalogue tops do not
repeat its finite kernel reductions. Declaration names are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads

/-- Realization-free finite declaration for paired8-1. -/
noncomputable def finiteCoupledHeadData :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTopCoupledRegistryData
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 4 where
  Generator := Fin 4
  State := Fin 11
  generators := topAmbient
  state := states
  registry := completeRegistry

/-- Catalogue-facing semantic package for the selected paired-eight row.
For every realization of the two successive pair frames, the generated
table now bounds the three actual omega axes attached to every original
normal subgroup. -/
noncomputable def towerCoupledHeadData
    {p : Non2UnipotentPrefixFiniteMenu.PreE7PairActionClass 16}
    (R : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTopTowerRealization
        Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top1 p) :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTopTowerCoupledHeadData R 4 :=
  finiteCoupledHeadData.towerData R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads

end
