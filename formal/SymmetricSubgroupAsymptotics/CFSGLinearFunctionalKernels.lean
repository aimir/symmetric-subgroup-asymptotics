import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Two nonzero linear forms with the same literal zero set differ
by a nonzero scalar. This elementary statement is independent of any
finite-dimensional or projective-geometry recognition theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem nonzero_smul_of_zero_iff (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hker : ∀ x, f x = 0 ↔ g x = 0) :
    ∃ c : K, c ≠ 0 ∧ f = c • g := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    apply LinearMap.ext
    intro x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hex
  have hgx : g x ≠ 0 := fun h => hx ((hker x).mpr h)
  refine ⟨f x / g x, div_ne_zero hx hgx, ?_⟩
  apply LinearMap.ext
  intro y
  have hz : f (f x • y - f y • x) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have he := (hker (f x • y - f y • x)).mp hz
  simp only [map_sub, map_smul, smul_eq_mul] at he
  change f y = (f x / g x) * g y
  calc
    f y = (f x * g y) / g x :=
      (eq_div_iff hgx).mpr (sub_eq_zero.mp he).symm
    _ = (f x / g x) * g y := by ring

end SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernels
