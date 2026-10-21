import SymmetricSubgroupAsymptotics.BooleanFourStrictSperner
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card

/-! Five-element Boolean-four antichains already lie in the middle
layer. A singleton leaves a Boolean-three antichain of size at most three;
complementation handles rank three. No families are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem boolean_four_antichain_card_le_four_of_singleton
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))))
    (i : Fin 4) (hi : {i} ∈ A) : A.card ≤ 4 := by
  classical
  let T := {j : Fin 4 // j ≠ i}
  let f : Finset (Fin 4) → Finset T := Finset.subtype (fun j => j ≠ i)
  let B := (A.erase {i}).image f
  have hnot (s : Finset (Fin 4)) (hs : s ∈ A.erase {i}) : i ∉ s := by
    intro his
    exact hA hi (Finset.mem_of_mem_erase hs) (Ne.symm (Finset.mem_erase.mp hs).1)
      (Finset.singleton_subset_iff.mpr his)
  have hpred (s : Finset (Fin 4)) (hs : s ∈ A.erase {i}) : ∀ j ∈ s, j ≠ i := by
    intro j hj he
    exact hnot s hs (he ▸ hj)
  have hf : Set.InjOn f (A.erase {i} : Set (Finset (Fin 4))) := by
    intro s hs t ht he
    have hm := congrArg (fun C : Finset T => C.map (Function.Embedding.subtype _)) he
    change (s.subtype (fun j => j ≠ i)).map _ = (t.subtype (fun j => j ≠ i)).map _ at hm
    rwa [Finset.subtype_map_of_mem (hpred s hs), Finset.subtype_map_of_mem (hpred t ht)] at hm
  have hB : IsAntichain (· ⊆ ·) (B : Set (Finset T)) := by
    intro a ha b hb hne hab
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    have hst : s ⊆ t := by
      intro j hj
      have hm : (⟨j, hpred s hs j hj⟩ : T) ∈ f s := Finset.mem_subtype.mpr hj
      exact Finset.mem_subtype.mp (hab hm)
    exact hA (Finset.mem_of_mem_erase hs) (Finset.mem_of_mem_erase ht)
      (fun he => hne (congrArg f he)) hst
  have hT : Fintype.card T = 3 := by
    simpa only [T, Fintype.card_fin, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun j : Fin 4 => j = i))
  have hb := hB.sperner
  rw [hT] at hb
  norm_num at hb
  have hc : (A.erase {i}).card = B.card := (Finset.card_image_of_injOn hf).symm
  have he := Finset.card_erase_add_one hi
  omega

theorem boolean_four_antichain_five_member_card
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))))
    (hcard : 5 ≤ A.card) (s : Finset (Fin 4)) (hs : s ∈ A) : s.card = 2 := by
  classical
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
  have hone : s.card ≠ 1 := by
    intro he
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp he
    have hb := boolean_four_antichain_card_le_four_of_singleton A hA i (hi ▸ hs)
    omega
  have hthree : s.card ≠ 3 := by
    intro he
    have hcomp : IsAntichain (· ⊆ ·) (A.image (compl : Finset (Fin 4) → Finset (Fin 4)) :
        Set (Finset (Fin 4))) := by
      simpa only [Finset.coe_image] using hA.image_compl
    have hsc : sᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, he]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsc
    have hmem : {i} ∈ A.image (compl : Finset (Fin 4) → Finset (Fin 4)) := by
      rw [← hi]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hb := boolean_four_antichain_card_le_four_of_singleton _ hcomp i hmem
    rw [Finset.card_image_of_injective A compl_injective] at hb
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
  omega

end SymmetricSubgroupAsymptotics
