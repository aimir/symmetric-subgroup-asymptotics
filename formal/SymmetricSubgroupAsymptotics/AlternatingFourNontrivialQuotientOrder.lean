import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingFourNontrivialQuotientOrder

theorem three_dvd {B : Type} [Group B] [Finite B]
    (f : alternatingGroup (Fin 4) →* B) (hf : Function.Surjective f)
    (hne : ∃ a, f a≠1) : 3 ∣ Nat.card B := by
  have hp := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hp
  have hc : Nat.card (alternatingGroup (Fin 4))=12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  rw [hc] at hp
  rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy f.ker inferInstance with h | h | h
  · rw [h] at hp
    have hb : Nat.card B=12 := by simpa using hp
    rw [hb]
    decide
  · rw [h,alternatingGroup.kleinFour_card_of_card_eq_four (by simp)] at hp
    have hb : Nat.card B=3 := by omega
    rw [hb]
  · obtain ⟨a,ha⟩ := hne
    exact (ha ((MonoidHom.mem_ker).mp (by rw [h]; exact Subgroup.mem_top a))).elim

private theorem klein_cubic_trivial : ∀ a : alternatingGroup (Fin 4),
    a ∈ alternatingGroup.kleinFour (Fin 4) → a^3=1 → a=1 := by
  have h : ∀ a : alternatingGroup (Fin 4), NaturalA4ScalarFourHead.top a=1 →
      a^3=1 → a=1 := by decide +kernel
  intro a ha hc
  rw [← NaturalA4ScalarFourHead.top_ker] at ha
  exact h a ha hc

theorem cubic_survives {B : Type} [Group B]
    (f : alternatingGroup (Fin 4) →* B) (hne : ∃ b, f b≠1)
    (a : alternatingGroup (Fin 4)) (ha : a^3=1) (han : a≠1) : f a≠1 := by
  intro hz
  have hm : a ∈ f.ker := hz
  rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy f.ker inferInstance with h | h | h
  · rw [h,Subgroup.mem_bot] at hm
    exact han hm
  · rw [h] at hm
    exact han (klein_cubic_trivial a hm ha)
  · obtain ⟨b,hb⟩ := hne
    exact hb ((MonoidHom.mem_ker).mp (by rw [h]; exact Subgroup.mem_top b))

end SymmetricSubgroupAsymptotics.AlternatingFourNontrivialQuotientOrder
