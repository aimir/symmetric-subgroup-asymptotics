import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension
import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
import Mathlib.GroupTheory.Abelianization.Finite

/-! An index-four normal subgroup retains its full integral relative
abelianization. Centralizing that subgroup leaves a group whose central
quotient has order at most four, so its derived subgroup has order at most
two. No reduction modulo two is used. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem normalIntegralCoinvariantOrder_double_le_abelianization_of_index_four
    (E : Subgroup G) [E.Normal] (hindex : E.index = 4) :
    2 * normalIntegralCoinvariantOrder E ≤ Nat.card (Abelianization G) := by
  let D : Subgroup G := ⁅E,⊤⁆
  let H := G ⧸ D
  let q := QuotientGroup.mk' D
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective D
  have hDE : D ≤ E := Subgroup.commutator_le_left E ⊤
  have hcentral : E.map q ≤ Subgroup.center H := by
    rintro _ ⟨e,he,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨g,rfl⟩ := hq x
    have hc : q ⁅e,g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.commutator_mem_commutator he (Subgroup.mem_top g))
    rw [map_commutatorElement] at hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
  have hiE : (E.map q).index = 4 := by
    rw [Subgroup.index_map_eq E hq (by simpa only [q,QuotientGroup.ker_mk'] using hDE)]
    exact hindex
  have hiZ : (Subgroup.center H).index ≤ 4 := by
    have h := Subgroup.index_dvd_of_le hcentral
    rw [hiE] at h
    exact Nat.le_of_dvd (by decide : 0 < 4) h
  have hd : Nat.card (commutator H) ≤ 2 := by
    by_cases hab : ∀ a b : H,a*b=b*a
    · letI : IsMulCommutative H := ⟨⟨hab⟩⟩
      rw [commutator_eq_bot H,Subgroup.card_bot]
      decide
    · have hlo := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hab
      have heq : (Subgroup.center H).index = 4 := by omega
      exact CentralIndexFourDerivedBound.commutator_card_le_two_of_center_index_four heq hab
  have hAb : Nat.card (Abelianization H) ≤ Nat.card (Abelianization G) := by
    apply Nat.card_le_card_of_surjective (Abelianization.map q)
    intro a
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (commutator H) a
    obtain ⟨g,rfl⟩ := hq h
    exact ⟨Abelianization.of g,Abelianization.map_of q g⟩
  have hH : Nat.card H ≤ Nat.card (Abelianization G) * 2 := by
    have hf := (commutator H).card_eq_card_quotient_mul_card_subgroup
    change Nat.card H = Nat.card (Abelianization H) * Nat.card (commutator H) at hf
    exact hf.le.trans (Nat.mul_le_mul hAb hd)
  have horder : normalIntegralCoinvariantOrder E * 4 = Nat.card H := by
    have hi := Subgroup.relIndex_mul_index hDE
    change normalIntegralCoinvariantOrder E * E.index = Nat.card H at hi
    simpa only [hindex] using hi
  nlinarith

theorem normalIntegralCoinvariantOrder_le_sixteen_of_index_four
    (E : Subgroup G) [E.Normal] (hindex : E.index = 4)
    (hAb : Nat.card (Abelianization G) ≤ 32) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  have h := normalIntegralCoinvariantOrder_double_le_abelianization_of_index_four E hindex
  omega

end SymmetricSubgroupAsymptotics
