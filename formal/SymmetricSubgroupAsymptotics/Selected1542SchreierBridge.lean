import SymmetricSubgroupAsymptotics.Selected1542FirstMonolith
import SymmetricSubgroupAsymptotics.Selected1542SecondCenterData
import SymmetricSubgroupAsymptotics.Selected1542TargetKernelCover

/-! The sparse second-center witnesses use the same nine actual original
Schreier words and the same exact original coset grid. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

set_option maxHeartbeats 1000000 in
private theorem secondCenterSchreier_receipt : ∀ (j : Fin 9) (p : Fin 16),
    secondCenterSchreier j p=firstCenterGenerator j p := by decide +kernel

theorem secondCenterSchreier_eq (j : Fin 9) : secondCenterSchreier j=firstCenterGenerator j :=
  Equiv.ext (secondCenterSchreier_receipt j)

theorem secondCenterZ_eq : secondCenterZ=firstCenterZ := rfl

theorem original_kernel_grid_val (r : Fin 16) (i : Fin 64) :
    (originalState (secondCenterTargetIndex r)*preimageOriginal i).val=
      secondCenterGrid ((finProdFinEquiv : Fin 16 × Fin 64 ≃ Fin 1024) (r,i)) := by
  change (originalState (secondCenterTargetIndex r)).val*preimageElements i=_
  rw [originalState_val]
  simp only [secondCenterGrid,Equiv.symm_apply_apply]

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
