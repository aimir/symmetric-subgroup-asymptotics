import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Two nonproportional linear functionals prescribe arbitrary two
values. The construction uses one normalized vector and one kernel
witness, with no finite-field cardinality or dimension premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoFunctionalPrescription
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_value_one (f : V →ₗ[K] K) (hf : f ≠ 0) : ∃ u, f u = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  refine ⟨(f v)⁻¹ • v, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]

theorem exists_kernel_witness (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hg : ∀ c : K, g ≠ c • f) : ∃ z, f z = 0 ∧ g z ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := exists_value_one f hf
  by_contra h
  push_neg at h
  apply hg (g u)
  apply LinearMap.ext
  intro x
  have hz : f (x - f x • u) = 0 := by
    rw [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
  have he := h (x - f x • u) hz
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at he
  change g x = g u * f x
  exact he.trans (mul_comm _ _)

theorem exists_pair_values (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hg : ∀ c : K, g ≠ c • f) (a b : K) :
    ∃ v, f v = a ∧ g v = b := by
  obtain ⟨u, hu⟩ := exists_value_one f hf
  obtain ⟨z, hz, hgz⟩ := exists_kernel_witness f g hf hg
  refine ⟨a • u + ((b - a * g u) / g z) • z, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hu, hz]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  · rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [div_mul_cancel₀ _ hgz]
    ring

end SymmetricSubgroupAsymptotics.CFSGTwoFunctionalPrescription
