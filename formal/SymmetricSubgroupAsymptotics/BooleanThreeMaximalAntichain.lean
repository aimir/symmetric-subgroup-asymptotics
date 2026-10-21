import SymmetricSubgroupAsymptotics.BooleanFourStrictSperner
import Mathlib.Data.Finset.Image

/-! A Boolean-three antichain with at least three members is a single
middle layer. The proof uses cardinalities and incomparability, without
enumerating families of subsets. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {α : Type} [Fintype α] [DecidableEq α]

private theorem boolean_three_member_middle
    (hα : Fintype.card α = 3) (A : Finset (Finset α))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α))) (hcard : 3 ≤ A.card)
    (s : Finset α) (hs : s ∈ A) : s.card = 1 ∨ s.card = 2 := by
  have hc : s.card ≤ 3 := (Finset.card_le_univ s).trans_eq hα
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
  have hthree : s.card ≠ 3 := by
    intro he
    have hem : s = Finset.univ := Finset.eq_univ_of_card s (he.trans hα.symm)
    have hsub : A ⊆ {s} := by
      intro t ht
      apply Finset.mem_singleton.mpr
      by_contra hne
      exact hA ht hs hne (by rw [hem]; exact Finset.subset_univ _)
    have hb := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hb
    omega
  omega

private theorem boolean_three_mixed_card_le_two
    (hα : Fintype.card α = 3) (A : Finset (Finset α))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (i : α) (hi : {i} ∈ A) (t : Finset α) (ht : t ∈ A) (htc : t.card = 2) :
    A.card ≤ 2 := by
  have hit : i ∉ t := by
    intro him
    have hne : ({i} : Finset α) ≠ t := by
      intro he
      have := congrArg Finset.card he
      simp only [Finset.card_singleton, htc] at this
      omega
    exact hA hi ht hne (Finset.singleton_subset_iff.mpr him)
  have htu : t = Finset.univ.erase i := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      exact Finset.mem_erase.mpr ⟨fun he => hit (he ▸ hj), Finset.mem_univ j⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hα, htc]
  have hsub : A ⊆ {{i}, t} := by
    intro s hs
    by_cases hsi : s = {i}
    · exact Finset.mem_insert.mpr (Or.inl hsi)
    · have his : i ∉ s := by
        intro him
        exact hA hi hs (Ne.symm hsi) (Finset.singleton_subset_iff.mpr him)
      have hst : s ⊆ t := by
        rw [htu]
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun he => his (he ▸ hj), Finset.mem_univ j⟩
      have he : s = t := by
        by_contra hne
        exact hA hs ht hne hst
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  have hb := Finset.card_le_card hsub
  rcases Finset.card_pair_eq_one_or_two (a := ({i} : Finset α)) (b := t) with he | he <;> omega

theorem boolean_three_antichain_uniform_middle
    (hα : Fintype.card α = 3) (A : Finset (Finset α))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α))) (hcard : 3 ≤ A.card) :
    (∀ s ∈ A, s.card = 1) ∨ (∀ s ∈ A, s.card = 2) := by
  classical
  by_cases hone : ∃ s ∈ A, s.card = 1
  · obtain ⟨s, hs, hsc⟩ := hone
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsc
    left
    intro t ht
    rcases boolean_three_member_middle hα A hA hcard t ht with h | h
    · exact h
    · have hb := boolean_three_mixed_card_le_two hα A hA i (hi ▸ hs) t ht h
      omega
  · right
    intro s hs
    rcases boolean_three_member_middle hα A hA hcard s hs with h | h
    · exact False.elim (hone ⟨s, hs, h⟩)
    · exact h

end SymmetricSubgroupAsymptotics
