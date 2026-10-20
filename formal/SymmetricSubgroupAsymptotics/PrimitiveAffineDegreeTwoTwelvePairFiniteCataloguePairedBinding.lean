import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueFiniteRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCataloguePairedSixInterfaces

/-! Exact binding of the two paired rows to their degree-six interfaces. -/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

private def pairedPosition : Fin 2 → Fin 301 := ![194, 235]

private abbrev PairedRowIndex := {j : Fin 301 // branch j = .paired}

private def pairedForward (j : PairedRowIndex) : Fin 2 :=
  if j.1.val = 194 then 0 else 1

private def pairedBackward (i : Fin 2) : PairedRowIndex :=
  ⟨pairedPosition i, by fin_cases i <;> decide +kernel⟩

private def pairedBranchBinding : PairedRowIndex ≃ Fin 2 where
  toFun := pairedForward
  invFun := pairedBackward
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairedBinding : {j : Fin 301 // (row j).branch = .paired} ≃ Fin 2 :=
  pairedBranchBinding

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
