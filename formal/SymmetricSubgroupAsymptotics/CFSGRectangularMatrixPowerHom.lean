import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom

/-! Rectangular integer exponent maps compose by matrix multiplication.
This keeps finite integral embedding certificates separate from concrete
field or matrix-group simplification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRectangularMatrixPowerHom
variable {I J L G : Type*} [Fintype I] [Fintype J] [Fintype L] [CommGroup G]

def matrixPowerHom (A : Matrix I J ℤ) : (J→G)→*(I→G) where
  toFun x i := ∏j,x j ^ A i j
  map_one' := by funext i; simp
  map_mul' x y := by funext i; simp [mul_zpow,Finset.prod_mul_distrib]

@[simp] theorem matrixPowerHom_apply (A : Matrix I J ℤ) (x : J→G) (i : I) :
    matrixPowerHom A x i=∏j,x j ^ A i j := rfl

private theorem zpow_sum (x : G) {S : Type*} (s : Finset S) (a : S→ℤ) :
    x^(∑j∈s,a j)=∏j∈s,x^(a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj,zpow_add,ih]

theorem matrixPowerHom_mul (A : Matrix I J ℤ) (B : Matrix J L ℤ) (x : L→G) :
    matrixPowerHom (A*B) x=matrixPowerHom A (matrixPowerHom B x) := by
  funext i
  simp only [matrixPowerHom_apply,Matrix.mul_apply,zpow_sum,zpow_mul]
  rw [Finset.prod_comm]
  simp only [←Finset.prod_zpow,←zpow_mul,mul_comm]

def coordinateEmbedding [DecidableEq J] (f : I→J) : Matrix I J ℤ :=
  fun i j => if j=f i then 1 else 0

theorem matrixPowerHom_coordinateEmbedding [DecidableEq J] (f : I→J) (x : J→G) (i : I) :
    matrixPowerHom (coordinateEmbedding f) x i=x (f i) := by
  simp only [matrixPowerHom_apply,coordinateEmbedding,apply_ite,zpow_one,zpow_zero]
  simp

end SymmetricSubgroupAsymptotics.CFSGRectangularMatrixPowerHom
