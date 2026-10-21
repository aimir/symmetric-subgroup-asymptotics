import SymmetricSubgroupAsymptotics.RelativeIntegralCyclicQuotient
import SymmetricSubgroupAsymptotics.BinarySmallTopCenterBounds

/-! Full integral relative coinvariants of proper normals in an actual
binary group of order at most32 and abelianization order at most8.
No reduction of cyclic factors modulo2 is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem integral_relativeIndex_mul_card
    {H : Type} [Group H] [Finite H] (T C : Subgroup H) (hCT : C ≤ T) :
    C.relIndex T * Nat.card C = Nat.card T := by
  have hc := (C.subgroupOf T).card_mul_index
  have he : Nat.card (C.subgroupOf T) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT).toEquiv
  rw [he] at hc
  exact (Nat.mul_comm _ _).trans hc

/-- A true integral order bound for EVERY proper original normal. -/
theorem small_binary_proper_normal_integral_order_le_four
    {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (hcard : Nat.card H ≤ 32) (hAb : Nat.card (Abelianization H) ≤ 8)
    (T : Subgroup H) [T.Normal] (hproper : T ≠ ⊤) :
    (⁅T, (⊤ : Subgroup H)⁆).relIndex T ≤ 4 := by
  have hidx : 2 ≤ T.index := T.one_lt_index_of_ne_top hproper
  by_cases hab : ∀ a b : H, a*b=b*a
  · letI smallBinaryIntegral_comm : IsMulCommutative H := ⟨⟨hab⟩⟩
    have he := relative_integral_order_mul_index_of_abelian_supplement T
      (⊤ : Subgroup H) (by simp)
    have hm : (⁅T, (⊤ : Subgroup H)⁆).relIndex T * 2 ≤ 8 :=
      (Nat.mul_le_mul_left _ hidx).trans (he.le.trans hAb)
    omega
  · have hcenter := BinarySmallTopCenterBounds.center_le_four hH hcard hAb hab
    by_cases htwo : T.index = 2
    · letI smallBinaryIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI smallBinaryIntegral_cyclicQuotient : IsCyclic (H ⧸ T) :=
        isCyclic_of_prime_card (by exact htwo)
      have he := relative_integral_order_mul_index_of_cyclic_quotient T
      rw [htwo] at he
      omega
    · obtain ⟨k, hk⟩ := (hH.to_quotient T).exists_card_eq
      change T.index = 2 ^ k at hk
      have hk2 : 2 ≤ k := by
        by_contra hn
        have hc : k = 0 ∨ k = 1 := by omega
        rcases hc with hc | hc
        · rw [hc] at hk
          change T.index = 1 at hk
          omega
        · rw [hc] at hk
          change T.index = 2 at hk
          exact htwo hk
      have hi4 : 4 ≤ T.index := by
        rw [hk]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk2
      have htcard : Nat.card T ≤ 8 := by
        have hc := T.card_mul_index
        have hm : Nat.card T * 4 ≤ 32 :=
          (Nat.mul_le_mul_left _ hi4).trans (hc.le.trans hcard)
        omega
      let C := ⁅T, (⊤ : Subgroup H)⁆
      by_cases hzero : C = ⊥
      · have hcentral : T ≤ Subgroup.center H := by
          have hh := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
          simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hh
        change C.relIndex T ≤ 4
        rw [hzero, Subgroup.relIndex_bot_left]
        exact (Subgroup.card_le_of_le hcentral).trans hcenter
      · have hc2 : 2 ≤ Nat.card C := C.one_lt_card_iff_ne_bot.mpr hzero
        have he := integral_relativeIndex_mul_card T C (Subgroup.commutator_le_left T (⊤ : Subgroup H))
        change C.relIndex T ≤ 4
        have hm : C.relIndex T * 2 ≤ 8 :=
          (Nat.mul_le_mul_left _ hc2).trans (he.le.trans htcard)
        omega

end SymmetricSubgroupAsymptotics
