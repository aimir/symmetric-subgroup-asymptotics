import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The subgroups of `S4` whose order is divisible by three

Only a 24-element permutation calculation is used: an element of order
three has exactly one fixed point. The order-six recognition then follows
by normality of its index-two cubic subgroup. No subgroup enumeration or
classification input is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Subgroup MulAction
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.DegreeSixThreePairFourPointSubgroups

private theorem cubic_unique_fixed : ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 → g ≠ 1 →
    ∃ p : Fin 4, ∀ x : Fin 4, g x = x ↔ x = p := by
  decide +kernel

theorem card_symmetric_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-- Every actual order-six subgroup of `S4` fixes a point and is `S3`. -/
def subgroupSixEquiv (H : Subgroup (Equiv.Perm (Fin 4)))
    (hH : Nat.card H = 6) : H ≃* Equiv.Perm (Fin 3) := Classical.choice <| by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
    (by rw [hH]; decide)
  let C : Subgroup H := Subgroup.zpowers g
  have hC : Nat.card C = 3 := (Nat.card_zpowers g).trans hg
  have hi : C.index = 2 := by
    have h := C.card_mul_index
    rw [hC, hH] at h
    omega
  letI : C.Normal := C.normal_of_index_eq_two hi
  have hgperm : orderOf (g : Equiv.Perm (Fin 4)) = 3 := by
    change orderOf (H.subtype g) = 3
    rw [orderOf_injective H.subtype H.subtype_injective g]
    exact hg
  have hgpow : (g : Equiv.Perm (Fin 4)) ^ 3 = 1 := by
    simpa only [hgperm] using pow_orderOf_eq_one (g : Equiv.Perm (Fin 4))
  have hgne : (g : Equiv.Perm (Fin 4)) ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hgperm
    norm_num at hgperm
  obtain ⟨p, hp⟩ := cubic_unique_fixed g hgpow hgne
  have hgp : (g : Equiv.Perm (Fin 4)) p = p := (hp p).mpr rfl
  have hCstab : C ≤ MulAction.stabilizer H p := by
    apply Subgroup.zpowers_le.mpr
    exact hgp
  have hfix : ∀ h : H, (h : Equiv.Perm (Fin 4)) p = p := by
    intro h
    have hc : h⁻¹ * g * h ∈ C := by
      simpa only [inv_inv] using
        Subgroup.Normal.conj_mem (H := C) inferInstance g
          (Subgroup.mem_zpowers g) h⁻¹
    have hcfix : (h⁻¹ * g * h) • p = p := hCstab hc
    have hh := congrArg (fun x : Fin 4 => h • x) hcfix
    have hgfix : (g : Equiv.Perm (Fin 4)) ((h : Equiv.Perm (Fin 4)) p) =
        (h : Equiv.Perm (Fin 4)) p := by
      simpa [smul_smul, mul_assoc] using hh
    exact (hp _).mp hgfix
  let s : Finset (Fin 4) := {p}ᶜ
  have hs : s.card = 3 := by
    change ({p}ᶜ : Finset (Fin 4)).card = 3
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  let j : Equiv.Perm ↥s →* Equiv.Perm (Fin 4) := Equiv.Perm.ofSubtype
  have hj : Function.Injective j := Equiv.Perm.ofSubtype_injective
  have hle : H ≤ j.range := by
    intro h hh
    rw [Equiv.Perm.mem_range_ofSubtype_iff]
    intro y hy
    change y ∈ s
    simp only [s, Finset.mem_compl, Finset.mem_singleton]
    intro hyp
    subst y
    exact (Equiv.Perm.mem_support.mp hy) (hfix ⟨h, hh⟩)
  have hcardj : Nat.card j.range = 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe, hs]
    decide
  have heq : H = j.range := Subgroup.eq_of_le_of_card_ge hle (by rw [hH, hcardj])
  exact ⟨(MulEquiv.subgroupCongr heq).trans
    ((MonoidHom.ofInjective hj).symm.trans (Finset.equivFinOfCardEq hs).permCongrHom)⟩

private theorem small_order_cases : ∀ n : Fin 25,
    3 ∣ n.val → n.val ∣ 24 →
      n.val = 3 ∨ n.val = 6 ∨ n.val = 12 ∨ n.val = 24 := by
  decide +kernel

inductive Model (G : Type) [Group G] : Type
  | cyclicThree (equiv : G ≃* CyclicThree)
  | symmetricThree (equiv : G ≃* Equiv.Perm (Fin 3))
  | alternatingFour (equiv : G ≃* NaturalA4ScalarFourHead.G)
  | symmetricFour (equiv : G ≃* Equiv.Perm (Fin 4))

/-- The four abstract models of an actual `S4` subgroup with a cubic
factor in its order. -/
def subgroupModel (J : Subgroup (Equiv.Perm (Fin 4)))
    (hthree : 3 ∣ Nat.card J) : Model J := Classical.choice <| by
  have hdiv : Nat.card J ∣ 24 := by
    simpa only [card_symmetric_four] using Subgroup.card_subgroup_dvd_card J
  have hle : Nat.card J ≤ 24 := Nat.le_of_dvd (by decide) hdiv
  rcases small_order_cases ⟨Nat.card J, by omega⟩ hthree hdiv with h | h | h | h
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨.cyclicThree (mulEquivOfPrimeCardEq h (by
      exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)))⟩
  · exact ⟨.symmetricThree (subgroupSixEquiv J h)⟩
  · change Nat.card J = 12 at h
    have hi : J.index = 2 := by
      have hc := J.card_mul_index
      rw [h, card_symmetric_four] at hc
      omega
    exact ⟨.alternatingFour
      (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))⟩
  · exact ⟨.symmetricFour ((MulEquiv.subgroupCongr
      (Subgroup.eq_top_of_card_eq J (h.trans card_symmetric_four.symm))).trans
      Subgroup.topEquiv)⟩

end SymmetricSubgroupAsymptotics.DegreeSixThreePairFourPointSubgroups

end
