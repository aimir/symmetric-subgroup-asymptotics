import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
import Mathlib.LinearAlgebra.Pi

/-! Every base-field linear functional on finitely many extension-field
coordinates has genuine multiplication coefficients relative to any
chosen nonzero base-field functional on the extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.FieldFunctionalCoordinateCoefficients

open FieldFunctionalMultiplicationDuality
variable {F K I : Type*} [Field F] [Field K] [Algebra F K]
  [Module.Finite F K] [DecidableEq I]

/-- The unique multiplication coefficient of one coordinate restriction. -/
def coefficient (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (I → K)) (i : I) : K :=
  (multiplicationEquiv f hf).symm (ℓ.comp (LinearMap.single F (fun _ : I => K) i))

theorem single_apply_eq (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (I → K)) (i : I) (x : K) :
    ℓ (Pi.single i x) = f (coefficient f hf ℓ i * x) := by
  have he := (multiplicationEquiv f hf).apply_symm_apply
    (ℓ.comp (LinearMap.single F (fun _ : I => K) i))
  have hx := congrArg (fun g : Module.Dual F K => g x) he
  exact hx.symm

/-- Reconstruction uses the actual coordinate decomposition, with no
extension-field linearity premise on the original functional. -/
theorem apply_eq_sum_coefficients [Fintype I]
    (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (I → K)) (s : I → K) :
    ℓ s = f (∑ i, coefficient f hf ℓ i * s i) := by
  calc
    ℓ s = ℓ (∑ i, Pi.single i (s i)) :=
      congrArg ℓ (Finset.univ_sum_single s).symm
    _ = ∑ i, ℓ (Pi.single i (s i)) := map_sum ℓ _ _
    _ = ∑ i, f (coefficient f hf ℓ i * s i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact single_apply_eq f hf ℓ i (s i)
    _ = f (∑ i, coefficient f hf ℓ i * s i) := (map_sum f _ _).symm

/-- Choosing the central-coordinate restriction itself as f normalizes
that coefficient to one, by genuine multiplication duality. -/
theorem coefficient_eq_one_of_single_eq (f : Module.Dual F K) (hf : f ≠ 0)
    (ℓ : Module.Dual F (I → K)) (i : I)
    (hi : ∀ x : K, ℓ (Pi.single i x) = f x) :
    coefficient f hf ℓ i = 1 := by
  apply multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro x
  change f (coefficient f hf ℓ i * x) = f (1 * x)
  simpa only [one_mul] using (single_apply_eq f hf ℓ i x).symm.trans (hi x)

end SymmetricSubgroupAsymptotics.FieldFunctionalCoordinateCoefficients
