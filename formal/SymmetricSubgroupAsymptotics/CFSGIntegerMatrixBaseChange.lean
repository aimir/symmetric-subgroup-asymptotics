import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-! Canonical scalar extension from literal integer matrices to matrices
over a commutative ring, constructed on the actual tensor product. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange
variable (K : Type*) [CommRing K] (I : Type*) [Fintype I] [DecidableEq I]

def coefficientMap : Matrix I I ℤ →ₗ[ℤ] Matrix I I K :=
  (Int.castRingHom K).mapMatrix.toAddMonoidHom.toIntLinearMap

def tensorMap : (K ⊗[ℤ] Matrix I I ℤ) →ₗ[K] Matrix I I K :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton K (Matrix I I ℤ →ₗ[ℤ] Matrix I I K) (coefficientMap K I))

@[simp] theorem tensorMap_tmul (a : K) (X : Matrix I I ℤ) :
    tensorMap K I (a ⊗ₜ[ℤ] X) = a • (coefficientMap K I X) := rfl

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange
