import SymmetricSubgroupAsymptotics.CyclicQuotientRelativeHeadTwo
import SymmetricSubgroupAsymptotics.BinaryNormalHeadOrderGap

/-! Original relative heads for an order32 group with small center and a
literal two-cyclic cover of its abelianization. No normal menu is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OrderThirtyTwoBinaryRelativeHeads
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

 theorem relative_head_le_two
    {G C D : Type} [Group G] [Finite G]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (hG : Nat.card G=32) (hcenter : Nat.card (Subgroup.center G)≤4)
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)
    (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤2 := by
  by_cases hsmall : Nat.card M≤8
  · by_cases hc : M≤Subgroup.center G
    · have hm : Nat.card M≤4 := (Nat.card_le_card_of_injective
        (Subgroup.inclusion hc) (Subgroup.inclusion_injective hc)).trans hcenter
      have h := (primeCharacters_pow_finrank_le_card 2 M).trans hm
      have hr : Module.finrank (ZMod 2) (PrimeCharacters 2 M)≤2 :=
        (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp h
      exact (Submodule.finrank_le _).trans hr
    · have hm := binaryNormalHeadMax_le_of_not_le_center M 2 (by simpa using hsmall) hc
      exact (primeNormalHeadMax_le_iff 2 M 2).mp hm M le_rfl
  by_cases ht : M=⊤
  · subst M
    letI : IsCyclic (G ⧸ (⊤ : Subgroup G)) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr ⟨1,by
        apply top_unique
        intro z _
        have hz : z=1 := by
          obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup G) z
          exact (QuotientGroup.eq_one_iff (N := (⊤ : Subgroup G)) g).mpr (Subgroup.mem_top g)
        rw [hz]
        exact (Subgroup.zpowers (1 : G ⧸ (⊤ : Subgroup G))).one_mem⟩
    exact relativeHead_le_two_of_cyclic_quotient_cyclicCover 2 cover hcover ⊤
  have hd : Nat.card M∣32 := hG ▸ M.card_subgroup_dvd_card
  have hb : Nat.card M≤32 := Nat.le_of_dvd (by decide) hd
  have hn : Nat.card M≠32 := fun h => ht (M.eq_top_of_card_eq (h.trans hG.symm))
  have h16 : Nat.card M=16 := by
    interval_cases h : Nat.card M <;> norm_num at *
  have hQ : Nat.card (G ⧸ M)=2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    rw [hG,h16] at h
    omega
  letI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card (p := 2) hQ
  exact relativeHead_le_two_of_cyclic_quotient_cyclicCover 2 cover hcover M
end SymmetricSubgroupAsymptotics.OrderThirtyTwoBinaryRelativeHeads
