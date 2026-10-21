import SymmetricSubgroupAsymptotics.BinaryPairElementaryTopIntegralDimension
import SymmetricSubgroupAsymptotics.RelativeIntegralIndexFour
import SymmetricSubgroupAsymptotics.QuotientCenterIntegralCoinvariants

/-! The two useful dimension budgets retain complete integral orders for
every original normal preimage of a nonabelian quotient center. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

omit F [MulAction.IsPretransitive U X] in
private theorem elementary_integral_index_ge_four (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] (hindex : 2 < N.index) : 4 ≤ N.index := by
  by_contra hh
  have hthree : N.index = 3 := by omega
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hd := N.index_dvd_card
  rw [hthree, hn] at hd
  have hbad := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at hbad

theorem elementary_top_large_index_integral_order_le_256_of_kernel_dimension_eleven
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 11)
    (hAb : Nat.card (Abelianization U) ≤ 1024)
    (N : Subgroup U) [N.Normal] (hindex : 2 < N.index) :
    normalIntegralCoinvariantOrder N ≤ 256 := by
  apply F.elementary_top_integral_order_le_256_of_dimension_index hU hpow 1
    (by decide) hK hAb N
  exact elementary_integral_index_ge_four hU N hindex

theorem elementary_top_large_index_integral_order_le_256_of_kernel_dimension_twelve
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 12)
    (hAb : Nat.card (Abelianization U) ≤ 512)
    (N : Subgroup U) [N.Normal] (hindex : 2 < N.index) :
    normalIntegralCoinvariantOrder N ≤ 256 := by
  by_cases hfour : N.index = 4
  · have hh := normalIntegralCoinvariantOrder_double_le_abelianization_of_index_four N hfour
    omega
  · have hi4 := elementary_integral_index_ge_four hU N hindex
    have hi8 : 8 ≤ N.index := by
      obtain ⟨k, hk⟩ := (hU.to_quotient N).exists_card_eq
      change N.index = 2 ^ k at hk
      have hk3 : 3 ≤ k := by
        by_contra hh
        have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hcases with hh | hh | hh
        · rw [hh] at hk
          change N.index = 1 at hk
          omega
        · rw [hh] at hk
          change N.index = 2 at hk
          omega
        · rw [hh] at hk
          change N.index = 4 at hk
          exact hfour hk
      rw [hk]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk3
    exact F.elementary_top_integral_order_le_256_of_dimension_index hU hpow 2
      (by decide) hK (hAb.trans (by decide)) N hi8

theorem elementary_top_quotient_center_le_256_of_kernel_dimension_eleven
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 11)
    (hAb : Nat.card (Abelianization U) ≤ 1024)
    (N : Subgroup U) [N.Normal] (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI elementaryElevenCenter_normal : E.Normal := hE
  exact F.elementary_top_large_index_integral_order_le_256_of_kernel_dimension_eleven
    hU hpow hK hAb E hindex

theorem elementary_top_quotient_center_le_256_of_kernel_dimension_twelve
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (hK : Module.finrank (ZMod 2) F.kernelSpace ≤ 12)
    (hAb : Nat.card (Abelianization U) ≤ 512)
    (N : Subgroup U) [N.Normal] (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 256 := by
  apply quotient_center_card_le_of_large_index_integral_bound 256 ?_ N hnonab
  intro E hE hindex
  letI elementaryTwelveCenter_normal : E.Normal := hE
  exact F.elementary_top_large_index_integral_order_le_256_of_kernel_dimension_twelve
    hU hpow hK hAb E hindex

end SymmetricSubgroupAsymptotics.BinaryPairFrame
