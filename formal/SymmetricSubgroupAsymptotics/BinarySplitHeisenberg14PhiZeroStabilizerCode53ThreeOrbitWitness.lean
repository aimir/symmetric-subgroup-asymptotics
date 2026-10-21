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

def orbitRows_code_53 : Fin 3 → Fin 256 := ![0,1,2]

private theorem sep_53_0_1 :
    rowAction (orbitRows_code_53 0) (sectionMap (binaryVectorOfMask 6 53)) -
      rowAction (orbitRows_code_53 1) (sectionMap (binaryVectorOfMask 6 53)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_53_0_2 :
    rowAction (orbitRows_code_53 0) (sectionMap (binaryVectorOfMask 6 53)) -
      rowAction (orbitRows_code_53 2) (sectionMap (binaryVectorOfMask 6 53)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_53_1_2 :
    rowAction (orbitRows_code_53 1) (sectionMap (binaryVectorOfMask 6 53)) -
      rowAction (orbitRows_code_53 2) (sectionMap (binaryVectorOfMask 6 53)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem reverse_sep_53 (x y : V) (h : x-y ∉ radical.space) :
    y-x ∉ radical.space := by
  intro hr
  apply h
  convert radical.space.neg_mem hr using 1 <;> abel

theorem orbit_separated_code_53 : ∀ i j : Fin 3, i ≠ j →
    rowAction (orbitRows_code_53 i) (sectionMap (binaryVectorOfMask 6 53)) -
      rowAction (orbitRows_code_53 j) (sectionMap (binaryVectorOfMask 6 53)) ∉ radical.space := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact sep_53_0_1
  · exact sep_53_0_2
  · exact reverse_sep_53 _ _ sep_53_0_1
  · exact False.elim (hij rfl)
  · exact sep_53_1_2
  · exact reverse_sep_53 _ _ sep_53_0_2
  · exact reverse_sep_53 _ _ sep_53_1_2
  · exact False.elim (hij rfl)

private theorem top_original_code_53 : ∀ i : Fin 3, ∃ j : Fin 32,
    topPermutation (orbitRows_code_53 i) = (BinaryEightOriginalRowActions.heisenbergRow j).val := by
  decide +kernel

theorem top_mem_code_53 (i : Fin 3) :
    topPermutation (orbitRows_code_53 i) ∈ BinaryEightOriginalRowActions.heisenbergH := by
  obtain ⟨j,hj⟩ := top_original_code_53 i
  rw [hj]
  exact (BinaryEightOriginalRowActions.heisenbergRow j).property

theorem offset_mem_code_53 : ∀ i : Fin 3,
    destinationOffset (orbitRows_code_53 i) ∈ (BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer
