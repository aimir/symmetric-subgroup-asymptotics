import Mathlib.GroupTheory.Commutator.Basic

/-! Actual normal subgroups meet a self-centralizing normal kernel.
Its literal monolith therefore lies in every nontrivial normal denominator.
This is the group passage used after the concrete module monolith proof. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

theorem normal_cover_of_selfCentralizing_monolith
    {G : Type} [Group G] (E D : Subgroup G) [E.Normal]
    (hcentralizer : Subgroup.centralizer (E : Set G) ≤ E)
    (hmonolith : ∀ H : Subgroup G, H.Normal → H ≤ E → H ≠ ⊥ → D ≤ H)
    (N : Subgroup G) (hN : N.Normal) (hne : N ≠ ⊥) : D ≤ N := by
  letI : N.Normal := hN
  have hmeet : N ⊓ E ≠ ⊥ := by
    intro hbot
    have hcomm : ⁅N, E⁆ = ⊥ := by
      apply le_antisymm _ bot_le
      exact (Subgroup.commutator_le_inf (H₁ := N) (H₂ := E)).trans (le_of_eq hbot)
    have hNE : N ≤ E :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcentralizer
    exact hne ((inf_eq_left.mpr hNE).symm.trans hbot)
  exact (hmonolith (N ⊓ E) inferInstance inf_le_right hmeet).trans inf_le_left

end SymmetricSubgroupAsymptotics
