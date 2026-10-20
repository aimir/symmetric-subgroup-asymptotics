import SymmetricSubgroupAsymptotics.BinaryNormalHeadOrderGap
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization

/-! Proper normal heads for order-four tops, and order-eight tops whose
center has order at most two. Only subgroup orders and ambient mixed
commutators are used; no normal-subgroup census is performed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallBinaryTopProperRelativeHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem proper_card_le {R : Type} [Group R] [Finite R]
    (n : ℕ) (hR : Nat.card R≤2*n) (M : Subgroup R) (hne : M≠⊤) : Nat.card M≤n := by
  obtain ⟨k,hk⟩ := M.card_subgroup_dvd_card
  have hp : 0<Nat.card M := Nat.card_pos
  have hRpos : 0<Nat.card R := Nat.card_pos
  have hn : Nat.card M≠Nat.card R := fun h => hne (M.eq_top_of_card_eq h)
  have htwo : 2≤k := by
    by_contra h
    have : k=0 ∨ k=1 := by omega
    rcases this with rfl | rfl <;> simp_all
  nlinarith

private theorem head_le_one_of_card {R : Type} [Group R] [Finite R]
    (M : Subgroup R) [M.Normal] (hM : Nat.card M≤2) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  have h := (primeCharacters_pow_finrank_le_card 2 M).trans hM
  have hr : Module.finrank (ZMod 2) (PrimeCharacters 2 M)≤1 :=
    (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp h
  exact (Submodule.finrank_le _).trans hr

theorem order_four {R : Type} [Group R] [Finite R]
    (hR : Nat.card R≤4) (M : Subgroup R) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 :=
  head_le_one_of_card M (proper_card_le 2 hR M hne)

theorem order_eight {R : Type} [Group R] [Finite R]
    (hR : Nat.card R≤8) (hcenter : Nat.card (Subgroup.center R)≤2)
    (M : Subgroup R) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  by_cases hc : M≤Subgroup.center R
  · apply head_le_one_of_card M
    exact (Nat.card_le_card_of_injective (Subgroup.inclusion hc)
      (Subgroup.inclusion_injective hc)).trans hcenter
  · have hM : Nat.card M≤2^(1+1) := by
      simpa using proper_card_le 4 hR M hne
    have hm := binaryNormalHeadMax_le_of_not_le_center M 1 hM hc
    exact ((primeNormalHeadMax_le_iff 2 M 1).mp hm) M le_rfl
end SymmetricSubgroupAsymptotics.SmallBinaryTopProperRelativeHead
