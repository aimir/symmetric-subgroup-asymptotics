import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces

/-! A selected 32-row mixed-commutator pilot. It checks only the actual
Heisenberg action on the augmentation kernel modulo the radical of axis13;
no subgroup census or multiplication table is generated. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedPilot
open BinaryHeisenbergEightNaturalHeads

private theorem pilot_rows :
    Fintype.card {i : Fin 32 // ∀ j : Fin (charts 12).1,
      rho (BinaryEightOriginalRowActions.heisenbergRow i)
        ((charts 12).2.inclusion (Pi.single j 1)) -
        (charts 12).2.inclusion (Pi.single j 1) ∈ (radicalCharts 13).2.space} ≤ 8 := by
  decide +kernel

theorem top_kernel_augmentation_radical13_le_eight :
    Nat.card {t : H // BinaryHeisenbergCoordinateTemplate.topPredicate
      BinaryHeisenbergEightSquareCarry.K12 BinaryHeisenbergEightSquareCarry.R13 t} ≤ 8 := by
  have hb := BinaryHeisenbergCoordinateTemplate.top_card_le
    (charts 12).2 (radicalCharts 13).2 _ rfl
  have hK : (charts 12).2.space = BinaryHeisenbergEightSquareCarry.K12 := kernel12_space
  have hb' := hb.trans pilot_rows
  simpa only [hK, radical13_space] using hb'

end SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedPilot
