import SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedPilot

/-! After the selected augmentation pilot, one analogous 32-row capacity
and two finite basis inclusions finish the original Heisenberg boundary.
The fifteen natural states were already proved complete. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedCapacities
open BinaryHeisenbergEightNaturalHeads

private theorem axis13_rows :
    Fintype.card {i : Fin 32 // ∀ j : Fin (charts 13).1,
      rho (BinaryEightOriginalRowActions.heisenbergRow i)
        ((charts 13).2.inclusion (Pi.single j 1)) -
        (charts 13).2.inclusion (Pi.single j 1) ∈ (radicalCharts 14).2.space} ≤ 8 := by
  decide +kernel

theorem top_kernel_axis13_radical14_le_eight :
    Nat.card {t : H // BinaryHeisenbergCoordinateTemplate.topPredicate
      BinaryHeisenbergEightSquareCarry.K13 BinaryHeisenbergEightSquareCarry.R14 t} ≤ 8 := by
  have hb := BinaryHeisenbergCoordinateTemplate.top_card_le
    (charts 13).2 (radicalCharts 14).2 _ rfl
  have hK : (charts 13).2.space = BinaryHeisenbergEightSquareCarry.K13 := kernel13_space
  have hb' := hb.trans axis13_rows
  simpa only [hK, radical14_space] using hb'

private theorem basis12_mem_large : ∀ i : Fin 15,
    7 ≤ (charts i).1 → ∀ j : Fin (charts 12).1,
      (charts 12).2.inclusion (Pi.single j 1) ∈ (charts i).2.space := by
  decide +kernel

private theorem basis13_mem_large : ∀ i : Fin 15,
    5 ≤ (charts i).1 → ∀ j : Fin (charts 13).1,
      (charts 13).2.inclusion (Pi.single j 1) ∈ (charts i).2.space := by
  decide +kernel

theorem kernel_contains12_of_finrank_ge_seven
    (W : Subrepresentation rho)
    (hdim : 7 ≤ Module.finrank (ZMod 2) W.toSubmodule) :
    BinaryHeisenbergEightSquareCarry.K12 ≤ W.toSubmodule := by
  obtain ⟨i, hi⟩ := complete W
  have hd : Module.finrank (ZMod 2) (states i).toSubmodule = (charts i).1 := by
    rw [states_space]
    exact (charts i).2.finrank
  have hdi : 7 ≤ (charts i).1 := by rw [hi] at hd; omega
  rw [← kernel12_space]
  change (charts 12).2.space ≤ W.toSubmodule
  rw [← hi, states_space]
  exact (charts 12).2.le_of_basis_mem _ (basis12_mem_large i hdi)

theorem kernel_contains13_of_finrank_ge_five
    (W : Subrepresentation rho)
    (hdim : 5 ≤ Module.finrank (ZMod 2) W.toSubmodule) :
    BinaryHeisenbergEightSquareCarry.K13 ≤ W.toSubmodule := by
  obtain ⟨i, hi⟩ := complete W
  have hd : Module.finrank (ZMod 2) (states i).toSubmodule = (charts i).1 := by
    rw [states_space]
    exact (charts i).2.finrank
  have hdi : 5 ≤ (charts i).1 := by rw [hi] at hd; omega
  rw [← kernel13_space]
  change (charts 13).2.space ≤ W.toSubmodule
  rw [← hi, states_space]
  exact (charts 13).2.le_of_basis_mem _ (basis13_mem_large i hdi)

end SymmetricSubgroupAsymptotics.BinaryHeisenbergIntegralMixedCapacities
