import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTopData

/-! Third bounded multiplication chunk for the action-169 pair top. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

theorem topRows_mul_sixty_ninety : ∀ (i j : Fin 120),
    60 ≤ i.val → i.val < 90 →
    topRows (((⟨i⟩ : Source) * (⟨j⟩ : Source)).index) =
      topRows i * topRows j := by
  native_decide

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
