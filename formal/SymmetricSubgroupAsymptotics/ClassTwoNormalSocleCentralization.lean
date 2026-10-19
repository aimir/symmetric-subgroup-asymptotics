import SymmetricSubgroupAsymptotics.AbelianNormalSocleCentralization

/-! A normal subgroup of class at most two centralizes the whole ambient
socle. The commutator with a minimal normal subgroup is either trivial or
the whole minimal subgroup; in the latter case class two forces that same
minimal subgroup into the centralizer, so the commutator is trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G]

/-- No solvability, elementary-kernel, or finite classification input. -/
theorem minimalNormal_le_centralizer_of_class_two_normal
    (K M : Subgroup G) [K.Normal]
    (hclass : ⁅K,K⁆≤Subgroup.centralizer (K : Set G))
    (hM : IsMinimalNormalSubgroup M) :
    M≤Subgroup.centralizer (K : Set G) := by
  letI : M.Normal := hM.1
  rcases minimalNormal_commutator_full_or_trivial K M hM with hfull | hzero
  · have hMK : M≤K := by
      rw [←hfull]
      exact Subgroup.commutator_le_left K M
    rw [←hfull]
    exact (Subgroup.commutator_mono le_rfl hMK).trans hclass
  · apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact hzero

theorem finiteGroupSocle_le_centralizer_of_class_two_normal
    (K : Subgroup G) [K.Normal]
    (hclass : ⁅K,K⁆≤Subgroup.centralizer (K : Set G)) :
    finiteGroupSocle G≤Subgroup.centralizer (K : Set G) := by
  unfold finiteGroupSocle
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M,hM,hx⟩
  exact minimalNormal_le_centralizer_of_class_two_normal K M hclass hM hx

end SymmetricSubgroupAsymptotics
