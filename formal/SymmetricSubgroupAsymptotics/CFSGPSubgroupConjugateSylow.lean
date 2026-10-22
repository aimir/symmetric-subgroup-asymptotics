import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! An actual p-subgroup is contained in a conjugate of a fixed actual
Sylow. The conjugation orientation is retained as a membership formula. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGPSubgroupConjugateSylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conjugator (P : Subgroup G) (hP : IsPGroup p P) (U : Sylow p G) :
    ∃ a : G, ∀ x ∈ P, a⁻¹ * x * a ∈ (U : Subgroup G) := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G U Q
  have he : (U : Subgroup G).map (MulAut.conj a).toMonoidHom = (Q : Subgroup G) := by
    have hh := congrArg (fun R : Sylow p G => (R : Subgroup G)) ha
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.pointwise_smul_def] using hh
  refine ⟨a, fun x hx => ?_⟩
  have h : x ∈ (U : Subgroup G).map (MulAut.conj a).toMonoidHom := by
    rw [he]
    exact hPQ hx
  rcases h with ⟨y, hy, hxy⟩
  have hxy' : a * y * a⁻¹ = x := hxy
  have hc : a⁻¹ * x * a = y := by rw [← hxy']; group
  rw [hc]
  exact hy

end SymmetricSubgroupAsymptotics.CFSGPSubgroupConjugateSylow
