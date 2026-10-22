import SymmetricSubgroupAsymptotics.CFSGAffineComponentBoundedOrderCapacity
import SymmetricSubgroupAsymptotics.CFSGAffineComponentThirtyTwoCapacity

/-! Uniform capacity for the SAME original imprimitive affine component
from local degree25 onward. This replaces the composition-length input by
actual order estimates and the degree32 Clifford argument. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

def of_localDegree_ge_twentyFive_sufficientOrder
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hHalf : TraceyAffineHalfInducedModuleInput) (hLog : TraceyAffineInducedModuleInput)
    (hRefined : TraceyRefinedInducedModuleInput) (hPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock (A:=preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : 25 ≤ Nat.card block.Fibre) : ComponentSource hHalf hLog hRefined hPerm block P := by
  by_cases hlarge : 1024 ≤ Nat.card block.Fibre
  · exact of_localDegree_ge_oneThousandTwentyFour_order hHalf hLog hRefined hPerm block P hlarge
  by_cases h32 : Nat.card block.Fibre=32
  · exact of_localDegree_thirtyTwo_order hindex hHalf hLog hRefined hPerm block P h32
  · exact of_bounded_localDegree_order_away_thirtyTwo hHalf hLog hRefined hPerm block P
      hr (by omega) h32

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource
