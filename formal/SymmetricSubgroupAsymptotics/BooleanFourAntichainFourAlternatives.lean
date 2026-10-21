import SymmetricSubgroupAsymptotics.BooleanFourAntichainFourSingleton

/-! Four necessary leading supports have only the standard rank or
singleton/cubic-star shapes. This is an abstract antichain argument;
neither invariant modules nor subset families are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem boolean_four_antichain_four_alternatives
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4)))) (hcard : 4 ≤ A.card) :
    (∀ s ∈ A, s.card = 1) ∨
    (∀ s ∈ A, s.card = 2) ∨
    (∀ s ∈ A, s.card = 3) ∨
    (∃ i : Fin 4, {i} ∈ A ∧ ∀ s ∈ A, s = {i} ∨ (s.card = 2 ∧ i ∉ s)) ∨
    (∃ i : Fin 4, ({i} : Finset (Fin 4))ᶜ ∈ A ∧
      ∀ s ∈ A, s = ({i} : Finset (Fin 4))ᶜ ∨ (s.card = 2 ∧ i ∈ s)) := by
  classical
  by_cases hone : ∃ s ∈ A, s.card = 1
  · obtain ⟨s, hs, hsc⟩ := hone
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsc
    rcases boolean_four_antichain_four_singleton A hA hcard i (hi ▸ hs) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi ▸ hs, h⟩)))
  by_cases hthree : ∃ s ∈ A, s.card = 3
  · obtain ⟨s, hs, hsc⟩ := hthree
    let B := A.image (compl : Finset (Fin 4) → Finset (Fin 4))
    have hB : IsAntichain (· ⊆ ·) (B : Set (Finset (Fin 4))) := by
      simpa only [B, Finset.coe_image] using hA.image_compl
    have hBc : 4 ≤ B.card := by
      change 4 ≤ (A.image (compl : Finset (Fin 4) → Finset (Fin 4))).card
      rw [Finset.card_image_of_injective A compl_injective]
      exact hcard
    have hsc' : sᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, hsc]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsc'
    have hiB : {i} ∈ B := by
      rw [← hi]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hiA : ({i} : Finset (Fin 4))ᶜ ∈ A := by
      have he : ({i} : Finset (Fin 4))ᶜ = s := by rw [← hi, compl_compl]
      rwa [he]
    rcases boolean_four_antichain_four_singleton B hB hBc i hiB with h | h
    · right; right; left
      intro t ht
      have hc := h tᶜ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
      rw [Finset.card_compl, Fintype.card_fin] at hc
      have hbound := Finset.card_le_univ t
      rw [Fintype.card_fin] at hbound
      omega
    · right; right; right; right
      refine ⟨i, hiA, ?_⟩
      intro t ht
      rcases h tᶜ (Finset.mem_image.mpr ⟨t, ht, rfl⟩) with he | ⟨hc, him⟩
      · left
        have he' := congrArg (compl : Finset (Fin 4) → Finset (Fin 4)) he
        simpa only [compl_compl] using he'
      · right
        rw [Finset.card_compl, Fintype.card_fin] at hc
        have hbound := Finset.card_le_univ t
        rw [Fintype.card_fin] at hbound
        refine ⟨by omega, ?_⟩
        simpa only [Finset.mem_compl, not_not] using him
  · right; left
    intro s hs
    have hc : s.card ≤ 4 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 4)
    have hzero : s.card ≠ 0 := by
      intro he
      have hem : s = ∅ := Finset.card_eq_zero.mp he
      have hsub : A ⊆ {s} := by
        intro t ht
        apply Finset.mem_singleton.mpr
        by_contra hne
        exact hA hs ht (Ne.symm hne) (by rw [hem]; exact Finset.empty_subset _)
      have hb := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hb
      omega
    have hfour : s.card ≠ 4 := by
      intro he
      have hem : s = Finset.univ := Finset.eq_univ_of_card s he
      have hsub : A ⊆ {s} := by
        intro t ht
        apply Finset.mem_singleton.mpr
        by_contra hne
        exact hA ht hs hne (by rw [hem]; exact Finset.subset_univ _)
      have hb := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hb
      omega
    have hnot1 : s.card ≠ 1 := fun he => hone ⟨s, hs, he⟩
    have hnot3 : s.card ≠ 3 := fun he => hthree ⟨s, hs, he⟩
    omega

end SymmetricSubgroupAsymptotics
