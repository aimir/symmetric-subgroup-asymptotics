import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange
import Mathlib.Algebra.Lie.BaseChange

/-! The literal tensor-to-matrix realization of an integral matrix Lie
homomorphism preserves brackets over EVERY field. No injectivity or
characteristic restriction occurs. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.IntegerMatrixLieBaseChange
variable {I : Type*} [Fintype I] [DecidableEq I]
  {L : Type*} [LieRing L]

/-- Ring coefficient maps preserve the commutator Lie bracket. -/
theorem mapMatrix_lie {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (X Y : Matrix I I R) :
    f.mapMatrix ⁅X, Y⁆ = ⁅f.mapMatrix X, f.mapMatrix Y⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul]

variable (f : L →ₗ⁅ℤ⁆ Matrix I I ℤ) (K : Type*) [Field K]

def realization : (K ⊗[ℤ] L) →ₗ[K] Matrix I I K :=
  (CFSGIntegerMatrixBaseChange.tensorMap K I).comp (f.toLinearMap.baseChange K)

theorem realization_tmul (a : K) (x : L) :
    realization f K (a ⊗ₜ[ℤ] x) = a • (Int.castRingHom K).mapMatrix (f x) := by
  rw [realization, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    CFSGIntegerMatrixBaseChange.tensorMap_tmul]
  rfl

private theorem tensor_add_lie (x y z : K ⊗[ℤ] L) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := LieRing.add_lie x y z

private theorem tensor_lie_add (x y z : K ⊗[ℤ] L) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := LieRing.lie_add x y z

private theorem tensor_zero_lie (y : K ⊗[ℤ] L) : ⁅(0 : K ⊗[ℤ] L), y⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : K ⊗[ℤ] L => ⁅x, y⁆)
    (fun x z => tensor_add_lie K x z y)).map_zero

private theorem tensor_lie_zero (x : K ⊗[ℤ] L) : ⁅x, (0 : K ⊗[ℤ] L)⁆ = 0 :=
  (AddMonoidHom.mk' (fun y : K ⊗[ℤ] L => ⁅x, y⁆)
    (tensor_lie_add K x)).map_zero

private theorem matrix_add_lie (x y z : Matrix I I K) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := LieRing.add_lie x y z

private theorem matrix_lie_add (x y z : Matrix I I K) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := LieRing.lie_add x y z

theorem realization_map_lie (x y : K ⊗[ℤ] L) :
    realization f K ⁅x, y⁆ = ⁅realization f K x, realization f K y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [tensor_zero_lie, map_zero, Ring.lie_def, zero_mul, mul_zero, sub_self]
  | add x z hx hz => simp only [tensor_add_lie, map_add, hx, hz, matrix_add_lie]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [tensor_lie_zero, map_zero, Ring.lie_def, zero_mul, mul_zero, sub_self]
    | add y z hy hz => simp only [tensor_lie_add, map_add, hy, hz, matrix_lie_add]
    | tmul b y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul ℤ K L L a b x y, realization_tmul,
        realization_tmul, realization_tmul, f.map_lie]
      rw [mapMatrix_lie]
      simp only [Ring.lie_def, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm a b]

def lieHom : (K ⊗[ℤ] L) →ₗ⁅K⁆ Matrix I I K where
  toLinearMap := realization f K
  map_lie' {x y} := realization_map_lie f K x y

end SymmetricSubgroupAsymptotics.IntegerMatrixLieBaseChange
