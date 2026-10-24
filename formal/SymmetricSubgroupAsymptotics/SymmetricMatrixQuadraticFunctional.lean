import SymmetricSubgroupAsymptotics.SymmetricMatrixCongruenceAction
import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Actual quadratic forms attached to genuine coefficient-field
linear functionals on symmetric matrices. Stabilization of the
base-field functional is tested on every scalar multiple of every
rank-one matrix; multiplication duality then recovers K-valued
quadratic preservation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.SymmetricMatrixQuadraticFunctional

open SymmetricMatrixCongruenceAction FieldFunctionalMultiplicationDuality
variable {K : Type*} [Field K] (n : ℕ)

def cross (u v : Fin n → K) : Space (K := K) n :=
  ⟨Matrix.vecMulVec u v + Matrix.vecMulVec v u, by
    change (Matrix.vecMulVec u v + Matrix.vecMulVec v u).transpose = _
    rw [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, add_comm]⟩

theorem rankOne_add (u v : Fin n → K) :
    rankOne n (u + v) = rankOne n u + rankOne n v + cross n u v := by
  apply Subtype.ext
  ext i j
  change (u i + v i) * (u j + v j) =
    u i * u j + v i * v j + (u i * v j + v i * u j)
  ring

/-- This quadratic form is constructed from an actual bilinear outer product. -/
def quadratic (L : Module.Dual K (Space (K := K) n)) : QuadraticForm K (Fin n → K) :=
  (L.comp (upperProjection n)).compQuadraticMap
    (LinearMap.BilinMap.toQuadraticMap
      (vecMulVecBilin K K : (Fin n → K) →ₗ[K]
        (Fin n → K) →ₗ[K] Matrix (Fin n) (Fin n) K))

@[simp] theorem quadratic_apply (L : Module.Dual K (Space (K := K) n))
    (v : Fin n → K) : quadratic n L v = L (rankOne n v) := by
  change L (upperProjection n (Matrix.vecMulVec v v)) = L (rankOne n v)
  exact congrArg L (upperProjection_symmetric n (rankOne n v))

/-- An offdiagonal restriction is the actual polar coefficient, in every characteristic. -/
theorem polar_eq_cross (L : Module.Dual K (Space (K := K) n))
    (u v : Fin n → K) : (quadratic n L).polarBilin u v = L (cross n u v) := by
  change quadratic n L (u + v) - quadratic n L u - quadratic n L v = _
  rw [quadratic_apply, quadratic_apply, quadratic_apply, rankOne_add, map_add, map_add]
  abel

variable {F : Type*} [Field F] [Algebra F K]

def functional (f : Module.Dual F K) (L : Module.Dual K (Space (K := K) n)) :
    Module.Dual F (Space (K := K) n) := f.comp (L.restrictScalars F)

theorem functional_scaled_rankOne (f : Module.Dual F K)
    (L : Module.Dual K (Space (K := K) n)) (t : K) (v : Fin n → K) :
    functional n f L (t • rankOne n v) = f (t * quadratic n L v) := by
  change f (L (t • rankOne n v)) = _
  rw [map_smul, quadratic_apply]
  rfl

/-- The entire functional is preserved, not only its values on unscaled rank-one points. -/
def preservers (f : Module.Dual F K) (L : Module.Dual K (Space (K := K) n)) :
    Subgroup (GeneralLinear (K := K) n) where
  carrier := {A | ∀ S : Space (K := K) n,
    functional n f L (congruenceLinearMap n A S) = functional n f L S}
  one_mem' := by intro S; rw [congruenceLinearMap_one]
  mul_mem' := by
    intro A B hA hB S
    rw [congruenceLinearMap_mul, hA, hB]
  inv_mem' := by
    intro A hA S
    have he := hA (congruenceLinearMap n A⁻¹ S)
    rw [← congruenceLinearMap_mul, mul_inv_cancel, congruenceLinearMap_one] at he
    exact he.symm

theorem preserver_isometry (f : Module.Dual F K) (hf : f ≠ 0)
    (L : Module.Dual K (Space (K := K) n)) (A : preservers n f L)
    (v : Fin n → K) : quadratic n L (A.val.val *ᵥ v) = quadratic n L v := by
  apply multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro t
  have he := A.property (t • rankOne n v)
  rw [(congruenceLinearMap n A.val).map_smul, rankOne_congruence,
    functional_scaled_rankOne, functional_scaled_rankOne] at he
  change f (quadratic n L (A.val.val *ᵥ v) * t) = f (quadratic n L v * t)
  simpa only [mul_comm] using he

end SymmetricSubgroupAsymptotics.SymmetricMatrixQuadraticFunctional
