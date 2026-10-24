import SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! The characteristic polynomial of the literal natural linear
representation is the characteristic polynomial of the SAME matrix.
This binds operator primary codes to actual matrix polynomial ranges. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.MatrixUnitCharacteristicPolynomial
variable (K I : Type*) [Field K] [Fintype I] [DecidableEq I]

theorem naturalLinearHom_charpoly (H : Subgroup (Matrix I I K)ˣ) (g : H) :
    (MatrixUnitBilinearIsometryOrderBound.naturalLinearHom K I H g).toLinearMap.charpoly =
      (g.val : Matrix I I K).charpoly := by
  have hm : (MatrixUnitBilinearIsometryOrderBound.naturalLinearHom K I H g).toLinearMap =
      Matrix.toLin' (g.val : Matrix I I K) := rfl
  rw [hm]
  exact Matrix.charpoly_toLin' (g.val : Matrix I I K)

end SymmetricSubgroupAsymptotics.MatrixUnitCharacteristicPolynomial
