import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerCountData
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer

def orbitRows_code_44 : Fin 3 → Fin 256 := ![0,2,8]

private theorem sep_44_0_1 :
    rowAction (orbitRows_code_44 0) (sectionMap (binaryVectorOfMask 6 44)) -
      rowAction (orbitRows_code_44 1) (sectionMap (binaryVectorOfMask 6 44)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_44_0_2 :
    rowAction (orbitRows_code_44 0) (sectionMap (binaryVectorOfMask 6 44)) -
      rowAction (orbitRows_code_44 2) (sectionMap (binaryVectorOfMask 6 44)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_44_1_2 :
    rowAction (orbitRows_code_44 1) (sectionMap (binaryVectorOfMask 6 44)) -
      rowAction (orbitRows_code_44 2) (sectionMap (binaryVectorOfMask 6 44)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem reverse_sep_44 (x y : V) (h : x-y ∉ radical.space) :
    y-x ∉ radical.space := by
  intro hr
  apply h
  convert radical.space.neg_mem hr using 1 <;> abel

theorem orbit_separated_code_44 : ∀ i j : Fin 3, i ≠ j →
    rowAction (orbitRows_code_44 i) (sectionMap (binaryVectorOfMask 6 44)) -
      rowAction (orbitRows_code_44 j) (sectionMap (binaryVectorOfMask 6 44)) ∉ radical.space := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact sep_44_0_1
  · exact sep_44_0_2
  · exact reverse_sep_44 _ _ sep_44_0_1
  · exact False.elim (hij rfl)
  · exact sep_44_1_2
  · exact reverse_sep_44 _ _ sep_44_0_2
  · exact reverse_sep_44 _ _ sep_44_1_2
  · exact False.elim (hij rfl)

private theorem top_original_code_44 : ∀ i : Fin 3, ∃ j : Fin 32,
    topPermutation (orbitRows_code_44 i) = (BinaryEightOriginalRowActions.heisenbergRow j).val := by
  decide +kernel

theorem top_mem_code_44 (i : Fin 3) :
    topPermutation (orbitRows_code_44 i) ∈ BinaryEightOriginalRowActions.heisenbergH := by
  obtain ⟨j,hj⟩ := top_original_code_44 i
  rw [hj]
  exact (BinaryEightOriginalRowActions.heisenbergRow j).property

theorem offset_mem_code_44 : ∀ i : Fin 3,
    destinationOffset (orbitRows_code_44 i) ∈ (BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer
