import Mathlib.GroupTheory.OrderOfElement

/-! Selected element-order existence transports through an ABSTRACT
group isomorphism. Concrete consumers pass the already checked witness
without rewriting order expressions inside a large matrix-model type. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.EquivSelectedElementOrder

theorem exists_dvd_orderOf {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (m : ℕ) (hB : ∃ b : B, m ∣ orderOf b) :
    ∃ a : A, m ∣ orderOf a := by
  obtain ⟨b,hb⟩ := hB
  refine ⟨e.symm b,?_⟩
  rw [e.symm.orderOf_eq]
  exact hb

end SymmetricSubgroupAsymptotics.EquivSelectedElementOrder
