import SymmetricSubgroupAsymptotics.FieldFunctionalCoordinateCoefficients
import Mathlib.LinearAlgebra.Dimension.Free

/-! Genuine scalar-extension reconstruction of arbitrary base-field
functionals. The reconstructed map is K-linear; the original functional
is only F-linear. Uniqueness is tested on every K-multiple of a vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.FiniteFieldFunctionalLift

open Module FieldFunctionalMultiplicationDuality FieldFunctionalCoordinateCoefficients
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [Module.Finite F K]

/-- Pull the actual F-linear functional to the coordinates of an actual K-basis. -/
def coordinateFunctional {I : Type*} [Fintype I] (b : Basis I K V)
    (ℓ : Module.Dual F V) : Module.Dual F (I → K) :=
  ℓ.comp (b.equivFun.symm.toLinearMap.restrictScalars F)

/-- Multiplication duality supplies one genuine K-coefficient for each basis row. -/
def linearLiftOfBasis {I : Type*} [Fintype I] [DecidableEq I]
    (b : Basis I K V) (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F V) : Module.Dual K V :=
  ∑ i, coefficient f hf (coordinateFunctional b ℓ) i • b.coord i

theorem linearLiftOfBasis_spec {I : Type*} [Fintype I] [DecidableEq I]
    (b : Basis I K V) (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F V) (v : V) :
    ℓ v = f (linearLiftOfBasis b f hf ℓ v) := by
  have he := apply_eq_sum_coefficients f hf (coordinateFunctional b ℓ) (b.equivFun v)
  have hleft : coordinateFunctional b ℓ (b.equivFun v) = ℓ v := by
    change ℓ (b.equivFun.symm (b.equivFun v)) = ℓ v
    rw [LinearEquiv.symm_apply_apply]
  rw [hleft] at he
  convert he using 1
  congr 1
  simp only [linearLiftOfBasis, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Basis.equivFun_apply, Basis.coord_apply]

/-- No injectivity of f is assumed: varying the K-scalar gives separation. -/
theorem linear_lift_unique (f : Module.Dual F K) (hf : f ≠ 0)
    (L M : Module.Dual K V) (h : ∀ v : V, f (L v) = f (M v)) : L = M := by
  apply LinearMap.ext
  intro v
  apply multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro t
  have ht := h (t • v)
  change f (L v * t) = f (M v * t)
  simpa only [map_smul, smul_eq_mul, mul_comm] using ht

theorem exists_unique_linear_lift [Module.Finite K V]
    (f : Module.Dual F K) (hf : f ≠ 0) (ℓ : Module.Dual F V) :
    ∃! L : Module.Dual K V, ∀ v : V, ℓ v = f (L v) := by
  let b := Module.finBasis K V
  refine ⟨linearLiftOfBasis b f hf ℓ, linearLiftOfBasis_spec b f hf ℓ, ?_⟩
  intro M hM
  exact linear_lift_unique f hf M (linearLiftOfBasis b f hf ℓ)
    (fun v => (hM v).symm.trans (linearLiftOfBasis_spec b f hf ℓ v))

/-- A genuinely normalized one-dimensional restriction normalizes its K-lift. -/
theorem lift_eq_one_of_normalized_restriction
    (f : Module.Dual F K) (hf : f ≠ 0) (ℓ : Module.Dual F V)
    (L : Module.Dual K V) (hL : ∀ v : V, ℓ v = f (L v))
    (z : V) (hz : ∀ t : K, ℓ (t • z) = f t) : L z = 1 := by
  apply multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro t
  have ht := (hL (t • z)).symm.trans (hz t)
  change f (L z * t) = f (1 * t)
  simpa only [map_smul, smul_eq_mul, one_mul, mul_one, mul_comm] using ht

end SymmetricSubgroupAsymptotics.FiniteFieldFunctionalLift
