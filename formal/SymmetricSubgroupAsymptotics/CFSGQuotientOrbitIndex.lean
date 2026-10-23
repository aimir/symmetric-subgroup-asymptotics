import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper

/-! The exact same-carrier orbit index behind the quotient-action upper
bound. This allows a proved geometric orbit count instead of charging
the entire action set. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper
variable {G Q X : Type*} [Group G] [Group Q] [Finite X] [MulAction G X]

theorem exists_proper_subgroup_of_moved_point_orbit (pi : G →* Q)
    (hpi : Function.Surjective pi) (x : X)
    (hker : ∀ g ∈ pi.ker, g • x = x) (g : G) (hmove : g • x ≠ x) :
    ∃ H : Subgroup Q, H ≠ ⊤ ∧ H.index = Nat.card (MulAction.orbit G x) := by
  let S : Subgroup G := MulAction.stabilizer G x
  have hS : S ≠ ⊤ := by
    intro h
    have hg : g ∈ S := by rw [h]; trivial
    exact hmove hg
  have hk : pi.ker ≤ S := hker
  refine ⟨S.map pi, ?_, ?_⟩
  · intro h
    have hc := Subgroup.comap_map_eq_self hk
    rw [h, Subgroup.comap_top] at hc
    exact hS hc.symm
  · rw [S.index_map_eq hpi hk, MulAction.index_stabilizer, Nat.card_coe_set_eq]

end SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper
