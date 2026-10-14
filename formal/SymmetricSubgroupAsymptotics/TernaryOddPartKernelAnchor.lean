import Mathlib.GroupTheory.Sylow

/-!
# A binary kernel when the odd part of the group order is three

Suppose `|G| = 2^a * 3`. If a normal subgroup has a quotient whose order
is divisible by three, Lagrange's theorem forces that literal subgroup to
be a binary group. Consequently every nonbinary normal subgroup contains
every ternary subgroup: its image in the quotient must be trivial.

In particular, a family of normal subgroups with trivial intersection has
a binary member. The index type need not be finite. Applied to kernels,
the conclusion concerns one of the original homomorphisms, with no change
of target or replacement of its kernel by an isomorphic group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A factor of three in the quotient leaves only a power of two in the
order of the actual normal subgroup. -/
theorem ternaryOddPart_isPGroup_two_of_three_dvd_quotient_card
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (N : Subgroup G) [N.Normal]
    (hthree : 3 ∣ Nat.card (G ⧸ N)) : IsPGroup 2 N := by
  have hmul : 3 * Nat.card N ∣ 3 * 2 ^ a := by
    have h := mul_dvd_mul_right hthree (Nat.card N)
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcard] at h
    simpa only [Nat.mul_comm] using h
  have hdiv : Nat.card N ∣ 2 ^ a :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3) hmul
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  exact IsPGroup.of_card hb

/-- A ternary subgroup either lies in the displayed normal subgroup, or
forces that normal subgroup itself to be binary. -/
theorem ternaryOddPart_isPGroup_two_or_le
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (N : Subgroup G) [N.Normal]
    (P : Subgroup G) (hP : IsPGroup 3 P) :
    IsPGroup 2 N ∨ P ≤ N := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases (hP.map (QuotientGroup.mk' N)).card_eq_or_dvd with hone | hthree
  · right
    have hbot : P.map (QuotientGroup.mk' N) = ⊥ :=
      (P.map (QuotientGroup.mk' N)).eq_bot_of_card_eq hone
    simpa only [QuotientGroup.ker_mk'] using
      (P.map_eq_bot_iff.mp hbot)
  · left
    exact ternaryOddPart_isPGroup_two_of_three_dvd_quotient_card hcard N
      (hthree.trans (P.map (QuotientGroup.mk' N)).card_subgroup_dvd_card)

/-- Every nonbinary normal subgroup contains any chosen Sylow three
subgroup of the original group. -/
theorem ternaryOddPart_sylow_three_le_of_not_isPGroup_two
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    (N : Subgroup G) [N.Normal] (hN : ¬ IsPGroup 2 N)
    (P : Sylow 3 G) : (P : Subgroup G) ≤ N :=
  (ternaryOddPart_isPGroup_two_or_le hcard N P P.isPGroup').resolve_left hN

/-- Normal subgroups with trivial intersection cannot all contain a fixed
nontrivial Sylow three subgroup. This applies to arbitrary index types. -/
theorem ternaryOddPart_exists_isPGroup_two_of_iInf_eq_bot
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    {ι : Type*} (N : ι → Subgroup G)
    (hnormal : ∀ i, (N i).Normal) (hfaithful : (⨅ i, N i) = ⊥) :
    ∃ i, IsPGroup 2 (N i) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := Sylow.nonempty.some
  have hthree : 3 ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_left 3 (2 ^ a)
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hthree
  by_contra hnone
  apply hPne
  apply le_antisymm _ bot_le
  rw [← hfaithful]
  apply le_iInf
  intro i
  letI : (N i).Normal := hnormal i
  exact ternaryOddPart_sylow_three_le_of_not_isPGroup_two hcard (N i)
    (fun hi ↦ hnone ⟨i, hi⟩) P

/-- A jointly faithful family of homomorphisms has one binary literal
kernel when the odd part of the source order is exactly three. The target
monoids may depend on the index. -/
theorem ternaryOddPart_exists_isPGroup_two_ker
    {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hcard : Nat.card G = 2 ^ a * 3)
    {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    (f : ∀ i, G →* M i)
    (hfaithful : ∀ g : G, (∀ i, f i g = 1) → g = 1) :
    ∃ i, IsPGroup 2 (f i).ker := by
  apply ternaryOddPart_exists_isPGroup_two_of_iInf_eq_bot hcard
    (fun i ↦ (f i).ker) (fun _ ↦ inferInstance)
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply hfaithful g
  simpa only [Subgroup.mem_iInf, MonoidHom.mem_ker] using hg

end SymmetricSubgroupAsymptotics

end
