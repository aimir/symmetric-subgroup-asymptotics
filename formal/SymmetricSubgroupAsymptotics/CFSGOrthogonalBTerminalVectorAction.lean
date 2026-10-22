import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTerminalWeyl
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates

/-! The original terminal B Weyl word creates a positive pivot from
a nonzero terminal negative coordinate, with its actual minus sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationTerminalWeyl
variable (K : Type) [Field K]

theorem terminalWeyl_positive_last (r : ℕ) (v : Index (r + 1) → K) :
    (((terminalWeyl K r).val : Mat K (r + 1)) *ᵥ v) (pos (r + 1) (Fin.last r)) =
      -v (neg (r + 1) (Fin.last r)) := by
  rw [terminalWeyl_val]
  simp only [terminalArray, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp [Function.update_apply, pos, neg, middle]
  <;> ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
