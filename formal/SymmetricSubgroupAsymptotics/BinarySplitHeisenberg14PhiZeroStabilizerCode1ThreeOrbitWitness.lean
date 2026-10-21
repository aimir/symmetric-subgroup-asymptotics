import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerCountData
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerCode1OrbitWitness
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

def orbitRows_code_1 : Fin 3 → Fin 256 := fun i =>
  code1OrbitRows ⟨i.val, by have hi := i.isLt; omega⟩

theorem orbit_separated_code_1 : ∀ i j : Fin 3, i ≠ j →
    rowAction (orbitRows_code_1 i) (sectionMap (binaryVectorOfMask 6 1)) -
      rowAction (orbitRows_code_1 j) (sectionMap (binaryVectorOfMask 6 1)) ∉ radical.space := by
  intro i j hij
  apply code1_orbit_images_separated
  intro he
  have heval : i.val = j.val := congrArg (fun x : Fin 4 => x.val) he
  exact hij (Fin.ext heval)

private theorem top_original_code_1 : ∀ i : Fin 3, ∃ j : Fin 32,
    topPermutation (orbitRows_code_1 i) = (BinaryEightOriginalRowActions.heisenbergRow j).val := by
  decide +kernel

theorem top_mem_code_1 (i : Fin 3) :
    topPermutation (orbitRows_code_1 i) ∈ BinaryEightOriginalRowActions.heisenbergH := by
  obtain ⟨j,hj⟩ := top_original_code_1 i
  rw [hj]
  exact (BinaryEightOriginalRowActions.heisenbergRow j).property

theorem offset_mem_code_1 : ∀ i : Fin 3,
    destinationOffset (orbitRows_code_1 i) ∈ (BinaryHeisenbergEightNaturalHeads.charts 14).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizer
