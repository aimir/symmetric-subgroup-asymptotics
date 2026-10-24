import SymmetricSubgroupAsymptotics.FiniteFieldFunctionalLift
import SymmetricSubgroupAsymptotics.SymmetricMatrixQuadraticFunctional
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! Reconstruct an arbitrary base-field functional on actual symmetric
matrices. Its normalized offdiagonal restriction gives a genuinely
nonzero K-valued polar coefficient; its actual full stabilizer preserves
the resulting quadratic form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalReconstruction

open SymmetricMatrixCongruenceAction SymmetricMatrixQuadraticFunctional
variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Module.Finite F K] (n : ℕ)

/-- Preserve the original F-linear functional on its entire actual domain. -/
def stabilizer (ℓ : Module.Dual F (Space (K := K) n)) :
    Subgroup (GeneralLinear (K := K) n) where
  carrier := {A | ∀ S : Space (K := K) n,
    ℓ (congruenceLinearMap n A S) = ℓ S}
  one_mem' := by intro S; rw [congruenceLinearMap_one]
  mul_mem' := by
    intro A B hA hB S
    rw [congruenceLinearMap_mul, hA, hB]
  inv_mem' := by
    intro A hA S
    have he := hA (congruenceLinearMap n A⁻¹ S)
    rw [← congruenceLinearMap_mul, mul_inv_cancel, congruenceLinearMap_one] at he
    exact he.symm

/-- Choosing the actual cross-coordinate restriction as f forces polar value one. -/
theorem exists_normalized_lift (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (Space (K := K) n)) (u v : Fin n → K)
    (hnorm : ∀ t : K, ℓ (t • cross n u v) = f t) :
    ∃ L : Module.Dual K (Space (K := K) n),
      (∀ S, ℓ S = f (L S)) ∧ (quadratic n L).polarBilin u v = 1 := by
  obtain ⟨L, hL, _⟩ := FiniteFieldFunctionalLift.exists_unique_linear_lift f hf ℓ
  refine ⟨L, hL, ?_⟩
  rw [polar_eq_cross]
  exact FiniteFieldFunctionalLift.lift_eq_one_of_normalized_restriction
    f hf ℓ L hL (cross n u v) hnorm

/-- The stabilizer is the SAME original functional stabilizer; scalar
extension is obtained by proof, rather than imposed on the annihilator. -/
theorem stabilizer_preserves_quadratic (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (Space (K := K) n))
    (L : Module.Dual K (Space (K := K) n)) (hL : ∀ S, ℓ S = f (L S))
    (A : stabilizer n ℓ) (v : Fin n → K) :
    quadratic n L (A.val.val *ᵥ v) = quadratic n L v := by
  let e : preservers n f L := ⟨A.val, by
    intro S
    change f (L (congruenceLinearMap n A.val S)) = f (L S)
    exact (hL _).symm.trans ((A.property S).trans (hL S))⟩
  exact preserver_isometry n f hf L e v

end SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalReconstruction
