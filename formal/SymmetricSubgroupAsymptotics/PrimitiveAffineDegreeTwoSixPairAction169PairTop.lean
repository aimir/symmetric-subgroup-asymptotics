import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTopMul0
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTopMul1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTopMul2
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTopMul3

/-!
# Selected six-pair action 169: pair-top assembly

The multiplication table is checked in four disjoint bounded chunks so no
single compiler process materializes the full `120 × 120 × 6` decision.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

/-- The executable six-block action of the literal row group. -/
def pairTop : Source →* Equiv.Perm (Fin 6) where
  toFun x := topRows x.index
  map_one' := by decide +kernel
  map_mul' := by
    rintro ⟨i⟩ ⟨j⟩
    by_cases h30 : i.val < 30
    · exact topRows_mul_lt_thirty i j h30
    by_cases h60 : i.val < 60
    · exact topRows_mul_thirty_sixty i j (by omega) h60
    by_cases h90 : i.val < 90
    · exact topRows_mul_sixty_ninety i j (by omega) h90
    · exact topRows_mul_ninety i j (by omega)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
