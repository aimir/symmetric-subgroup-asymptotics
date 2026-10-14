import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Two complementary submodules separated by an actual acting scalar
share generator positions. This is the module analogue of retaining
orthogonal character components: the projector recovers each component
from the sum of their selected generators. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

/-- If an acting scalar is identity on P and zero on Q, the two generating
tuples can occupy the same positions. No semisimplicity is assumed. -/
theorem of_projected_submodules (P Q : Submodule R M) (a : R)
    (hP : ∀ x : P, a • (x : M) = x)
    (hQ : ∀ x : Q, a • (x : M) = 0)
    (hsup : P ⊔ Q = ⊤) (n : ℕ)
    (hgenP : ModuleGeneratedBy R P n) (hgenQ : ModuleGeneratedBy R Q n) :
    ModuleGeneratedBy R M n := by
  obtain ⟨u, hu⟩ := hgenP
  obtain ⟨v, hv⟩ := hgenQ
  let w : Fin n → M := fun i ↦ (u i : M) + (v i : M)
  let N := Submodule.span R (Set.range w)
  have hw (i : Fin n) : w i ∈ N := Submodule.subset_span ⟨i, rfl⟩
  have huN (i : Fin n) : (u i : M) ∈ N := by
    have h := N.smul_mem a (hw i)
    simpa only [w, smul_add, hP, hQ, add_zero] using h
  have hvN (i : Fin n) : (v i : M) ∈ N := by
    have h := N.sub_mem (hw i) (huN i)
    simpa only [w, add_sub_cancel_left] using h
  have hPN : P ≤ N := by
    have h : Submodule.span R (Set.range u) ≤ N.comap P.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact huN i
    rw [hu] at h
    intro x hx
    exact h (show (⟨x, hx⟩ : P) ∈ (⊤ : Submodule R P) from Submodule.mem_top)
  have hQN : Q ≤ N := by
    have h : Submodule.span R (Set.range v) ≤ N.comap Q.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hvN i
    rw [hv] at h
    intro x hx
    exact h (show (⟨x, hx⟩ : Q) ∈ (⊤ : Submodule R Q) from Submodule.mem_top)
  refine ⟨w, top_unique ?_⟩
  rw [← hsup]
  exact sup_le hPN hQN

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
