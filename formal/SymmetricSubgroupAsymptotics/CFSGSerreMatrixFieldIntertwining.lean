import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixOperators
import SymmetricSubgroupAsymptotics.CFSGSerreFieldTensor

/-! Coefficient automorphisms intertwine the original tensor space and
every proved integral square-zero matrix realization. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

theorem baseChange_semilinear (D : Data A I) (K : Type) [Field K] (σ : K ≃+* K)
    (x : Space A K) :
    baseChange D K (CFSGSerreField.semilinearEquiv A K σ x) =
      σ.toRingHom.mapMatrix (baseChange D K x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [CFSGSerreField.semilinearEquiv_tmul, baseChange_tmul, baseChange_tmul]
    ext i j
    change σ a * ((integralRepresentation D x i j : ℤ) : K) =
      σ (a * ((integralRepresentation D x i j : ℤ) : K))
    rw [map_mul, map_intCast]
  | add x y hx hy => simp only [map_add, hx, hy]

end SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
