import SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizerCountData
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantOriginalRows
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
namespace SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizer

def orbitRows_code_88 : Fin 3 → Fin 128 := ![0,1,2]

private theorem sep_88_0_1 :
    rowAction (orbitRows_code_88 0) (sectionMap (binaryVectorOfMask 8 88)) -
      rowAction (orbitRows_code_88 1) (sectionMap (binaryVectorOfMask 8 88)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_88_0_2 :
    rowAction (orbitRows_code_88 0) (sectionMap (binaryVectorOfMask 8 88)) -
      rowAction (orbitRows_code_88 2) (sectionMap (binaryVectorOfMask 8 88)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem sep_88_1_2 :
    rowAction (orbitRows_code_88 1) (sectionMap (binaryVectorOfMask 8 88)) -
      rowAction (orbitRows_code_88 2) (sectionMap (binaryVectorOfMask 8 88)) ∉ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem reverse_sep_88 (x y : V) (h : x-y ∉ radical.space) :
    y-x ∉ radical.space := by
  intro hr
  apply h
  convert radical.space.neg_mem hr using 1 <;> abel

theorem orbit_separated_code_88 : ∀ i j : Fin 3, i ≠ j →
    rowAction (orbitRows_code_88 i) (sectionMap (binaryVectorOfMask 8 88)) -
      rowAction (orbitRows_code_88 j) (sectionMap (binaryVectorOfMask 8 88)) ∉ radical.space := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact sep_88_0_1
  · exact sep_88_0_2
  · exact reverse_sep_88 _ _ sep_88_0_1
  · exact False.elim (hij rfl)
  · exact sep_88_1_2
  · exact reverse_sep_88 _ _ sep_88_0_2
  · exact reverse_sep_88 _ _ sep_88_1_2
  · exact False.elim (hij rfl)

theorem top_mem_code_88 (i : Fin 3) :
    topPermutation (orbitRows_code_88 i) ∈ BinaryEightOriginalRowActions.regularH :=
  BinarySplitRegular46FullConstantOriginalRows.top_mem _

theorem offset_mem_code_88 (i : Fin 3) :
    destinationOffset (orbitRows_code_88 i) ∈ (BinaryRegularEightNaturalRegistry.charts 46).2.space :=
  BinarySplitRegular46FullConstantOriginalRows.offset_mem _

end SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizer
