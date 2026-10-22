import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! Integer matrices act on finite products of a commutative group by
monomials.  This is the literal exponent map used by diagonal root scalings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom

variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

/-- The monomial map with the displayed integer exponent matrix. -/
def powerHom (A : Matrix I I ℤ) : (I → G) →* (I → G) where
  toFun x i := ∏ j, x j ^ A i j
  map_one' := by ext i; simp
  map_mul' x y := by ext i; simp [mul_zpow, Finset.prod_mul_distrib]

@[simp] theorem powerHom_apply (A : Matrix I I ℤ) (x : I → G) (i : I) :
    powerHom A x i = ∏ j, x j ^ A i j := rfl

variable [DecidableEq I]

@[simp] theorem powerHom_one (x : I → G) : powerHom (1 : Matrix I I ℤ) x = x := by
  classical
  ext i
  simp [powerHom, Matrix.one_apply]

private theorem zpow_sum (x : G) {J : Type*} (s : Finset J) (a : J → ℤ) :
    x ^ (∑ j ∈ s, a j) = ∏ j ∈ s, x ^ a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj, zpow_add, ih]

@[simp] theorem powerHom_mul (A B : Matrix I I ℤ) (x : I → G) :
    powerHom (A * B) x = powerHom A (powerHom B x) := by
  classical
  ext i
  simp only [powerHom_apply, Matrix.mul_apply, zpow_sum, zpow_mul]
  rw [Finset.prod_comm]
  simp only [← Finset.prod_zpow, ← zpow_mul, mul_comm]

/-- Diagonal matrices give the individual integer power maps. -/
@[simp] theorem powerHom_diagonal (a : I → ℤ) (x : I → G) (i : I) :
    powerHom (Matrix.diagonal a) x i = x i ^ a i := by
  classical
  simp [powerHom, Matrix.diagonal_apply]

/-- A right-inverse integer matrix gives a right-inverse monomial map. -/
theorem powerHom_rightInverse (V W : Matrix I I ℤ) (hVW : V * W = 1) :
    Function.RightInverse (powerHom W : (I → G) → (I → G)) (powerHom V) := by
  intro x
  rw [← powerHom_mul, hVW, powerHom_one]

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom
