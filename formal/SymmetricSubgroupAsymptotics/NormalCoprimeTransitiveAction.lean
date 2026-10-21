import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.GCD.Basic

/-! A normal subgroup of order coprime to a faithful transitive point
degree is trivial. The actual normal orbits remain original point blocks. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
  [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem normal_eq_bot_of_card_coprime_degree (N : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card X)) : N = ⊥ := by
  have hfix (x : X) : (MulAction.orbit N x).Subsingleton := by
    have hgroup : (MulAction.orbit N x).ncard ∣ Nat.card N := by
      rw [←MulAction.index_stabilizer N x]
      exact (MulAction.stabilizer N x).index_dvd_card
    have hdegree : (MulAction.orbit N x).ncard ∣ Nat.card X :=
      (MulAction.IsBlock.orbit_of_normal (G := G) (N := N) x).ncard_dvd_card ⟨x,MulAction.mem_orbit_self x⟩
    have hone : (MulAction.orbit N x).ncard = 1 :=
      Nat.eq_one_of_dvd_coprimes hcoprime hgroup hdegree
    exact Set.ncard_le_one_iff_subsingleton.mp hone.le
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  simpa only [one_smul] using
    hfix x (MulAction.mem_orbit x (⟨g,hg⟩ : N)) (MulAction.mem_orbit_self x)

end SymmetricSubgroupAsymptotics
end
