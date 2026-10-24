import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! The existing literal integer-matrix tensor map is a linear
equivalence over every commutative ring. This identifies actual matrix
reduction with scalar extension, independently of characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv
variable (K:Type*) [CommRing K] (I:Type*) [Fintype I] [DecidableEq I]

def equiv : (K⊗[ℤ]Matrix I I ℤ)≃ₗ[K]Matrix I I K :=
  (TensorProduct.piRight ℤ K K (fun _:I=>I→ℤ)).trans
    (LinearEquiv.piCongrRight fun _:I=>TensorProduct.piScalarRight ℤ K K I)

theorem equiv_tmul (a:K) (M:Matrix I I ℤ) :
    equiv K I (a⊗ₜ[ℤ]M)=CFSGIntegerMatrixBaseChange.tensorMap K I (a⊗ₜ[ℤ]M) := by
  ext i j
  change TensorProduct.piScalarRight ℤ K K I
    ((TensorProduct.piRight ℤ K K (fun _:I=>I→ℤ)) (a⊗ₜ[ℤ]M) i) j=a*(M i j:K)
  rw [TensorProduct.piRight_apply,TensorProduct.piRightHom_tmul,
    TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]
  change (M i j) • a=a*(M i j:K)
  rw [zsmul_eq_mul,mul_comm]

theorem equiv_eq_tensorMap : (equiv K I).toLinearMap=CFSGIntegerMatrixBaseChange.tensorMap K I := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero]
  | tmul a M=>exact equiv_tmul K I a M
  | add x y hx hy=>simp only [map_add,hx,hy]

theorem tensorMap_injective : Function.Injective (CFSGIntegerMatrixBaseChange.tensorMap K I) := by
  rw [← equiv_eq_tensorMap]
  exact (equiv K I).injective

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv
