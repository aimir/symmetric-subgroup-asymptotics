import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootScaling
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUpperShearForm

/-! Faithful original highest-root parameters and their exact upper
shear coordinates, including the unchanged B middle coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

theorem highestRoot_zero (h2 : (2 : K) ≠ 0) (s : ℕ) : highestRoot (K := K) s 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [highestRoot_val h2]
  simp

theorem highestRoot_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (highestRoot (K := K) s) := by
  intro a b hab
  have he := congrArg (fun u : elementaryRootGroup K (s + 3) =>
    (u.val : Mat K (s + 3)) (pos (s + 3) 0) (neg (s + 3) (secondIndex s))) hab
  dsimp only at he
  rw [highestRoot_val h2, highestRoot_val h2] at he
  simpa [pos, neg, secondIndex, Fin.ext_iff, Matrix.one_apply, Matrix.single_apply,
    Matrix.smul_apply, smul_eq_mul] using he

theorem highestRoot_eq_upperShear (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    ((highestRoot (K := K) s a).val : Mat K (s + 3)) =
      upperShearMatrix (s + 3)
        (Matrix.single 0 (secondIndex s) a - Matrix.single (secondIndex s) 0 a) := by
  rw [highestRoot_val h2]
  ext x y
  rcases x with (i | i) | ⟨⟩ <;> rcases y with (j | j) | ⟨⟩ <;>
    simp [upperShearMatrix, pos, neg, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, mul_ite]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
