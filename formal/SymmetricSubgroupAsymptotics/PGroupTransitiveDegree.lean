import Mathlib.GroupTheory.PGroup

/-! The original transitive action of a p-group has prime-power degree.
The action need not be faithful and the group need not be finite. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} {G X : Type*} [Group G] [MulAction G X] [Finite X]

theorem pGroup_transitive_degree [Fact p.Prime] (hG : IsPGroup p G) (x : X)
    (htrans : ∀ y : X, ∃ g : G, g • x = y) :
    ∃ k : ℕ, Nat.card X = p ^ k := by
  let e : MulAction.orbit G x ≃ X := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun y => ⟨⟨y, htrans y⟩, rfl⟩⟩
  obtain ⟨k, hk⟩ := hG.card_orbit x
  exact ⟨k, (Nat.card_congr e).symm.trans hk⟩

theorem binary_transitive_degree_ne_three (hG : IsPGroup 2 G) (x : X)
    (htrans : ∀ y : X, ∃ g : G, g • x = y) : Nat.card X ≠ 3 := by
  obtain ⟨k, hk⟩ := pGroup_transitive_degree hG x htrans
  intro hthree
  have hdvd : 3 ∣ 2 ^ k := by rw [← hk, hthree]
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
  norm_num at hbad

end SymmetricSubgroupAsymptotics

end
