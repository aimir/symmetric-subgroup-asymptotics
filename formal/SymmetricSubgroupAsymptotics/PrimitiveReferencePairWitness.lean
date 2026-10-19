import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem two_pretransitive_of_reference_pair
    {G X : Type*} [Group G] [MulAction G X] (a b : X)
    (h : ∀ x y : X, x ≠ y → ∃ g : G, g • a = x ∧ g • b = y) :
    MulAction.IsMultiplyPretransitive G X 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y z t hxy hzt
  obtain ⟨p,hp0,hp1⟩ := h x y hxy
  obtain ⟨q,hq0,hq1⟩ := h z t hzt
  have hpx : p⁻¹ • x = a := by rw [← hp0]; simp
  have hpy : p⁻¹ • y = b := by rw [← hp1]; simp
  exact ⟨q * p⁻¹, by simpa only [mul_smul,hpx] using hq0,
    by simpa only [mul_smul,hpy] using hq1⟩

end SymmetricSubgroupAsymptotics
