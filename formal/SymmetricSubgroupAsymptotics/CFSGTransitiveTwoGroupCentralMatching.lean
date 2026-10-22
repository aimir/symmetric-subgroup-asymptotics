import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.Transitive

/-! The actual central matching in a faithful transitive two-group action.
A nonidentity central element is fixed-point-free, and Cauchy's theorem
supplies a central involution. These are action-level facts, independent
of classification and of any Sylow-normalizer conclusion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTransitiveTwoGroupCentralMatching
open MulAction

theorem central_ne_one_has_no_fixed_point
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    [IsPretransitive G X] {z : G} (hz : z ∈ Subgroup.center G) (hne : z ≠ 1)
    (x : X) : z • x ≠ x := by
  intro hx
  apply hne
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  calc
    z • (g • x) = (z * g) • x := (mul_smul z g x).symm
    _ = (g * z) • x := by rw [← Subgroup.mem_center_iff.mp hz g]
    _ = g • (z • x) := mul_smul g z x
    _ = (1 : G) • (g • x) := by rw [hx, one_smul]

theorem exists_central_involution
    {G : Type*} [Group G] [Finite G] [Nontrivial G] (hG : IsPGroup 2 G) :
    ∃ z : G, z ∈ Subgroup.center G ∧ orderOf z = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hcenter : IsPGroup 2 (Subgroup.center G) := hG.to_subgroup _
  have hd : 2 ∣ Nat.card (Subgroup.center G) := by
    rcases hcenter.card_eq_or_dvd with h | h
    · have hlt : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
      omega
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 hd
  exact ⟨z, z.property, (Subgroup.orderOf_coe z).trans hz⟩

theorem exists_fixed_point_free_involution
    {G X : Type*} [Group G] [Finite G] [Nontrivial G]
    [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    (hG : IsPGroup 2 G) :
    ∃ z : G, z ∈ Subgroup.center G ∧ z ^ 2 = 1 ∧ ∀ x : X, z • x ≠ x := by
  obtain ⟨z, hz, horder⟩ := exists_central_involution hG
  have hne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    omega
  exact ⟨z, hz, by simpa only [horder] using pow_orderOf_eq_one z,
    central_ne_one_has_no_fixed_point hz hne⟩

end SymmetricSubgroupAsymptotics.CFSGTransitiveTwoGroupCentralMatching
