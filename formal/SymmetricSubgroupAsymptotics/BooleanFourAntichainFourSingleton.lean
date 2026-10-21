import SymmetricSubgroupAsymptotics.BooleanThreeMaximalAntichain
import Mathlib.Data.Fintype.Card

/-! The singleton case of a four-member Boolean-four antichain reduces
to a maximal Boolean-three antichain. This retains the distinguished
variable, rather than changing the original polynomial coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem boolean_four_antichain_four_singleton
    (A : Finset (Finset (Fin 4)))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))))
    (hcard : 4 ≤ A.card) (i : Fin 4) (hi : {i} ∈ A) :
    (∀ s ∈ A, s.card = 1) ∨
      (∀ s ∈ A, s = {i} ∨ (s.card = 2 ∧ i ∉ s)) := by
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
  have hc : B.card = (A.erase {i}).card := Finset.card_image_of_injOn hf
  have hthree : 3 ≤ B.card := by
    have he := Finset.card_erase_add_one hi
    omega
  have hfc (s : Finset (Fin 4)) (hs : s ∈ A.erase {i}) : (f s).card = s.card := by
    have hm := Finset.subtype_map_of_mem (hpred s hs)
    have he := congrArg Finset.card hm
    simpa only [Finset.card_map, f] using he
  rcases boolean_three_antichain_uniform_middle hT B hB hthree with hone | htwo
  · left
    intro s hs
    by_cases he : s = {i}
    · rw [he, Finset.card_singleton]
    · have hes : s ∈ A.erase {i} := Finset.mem_erase.mpr ⟨he, hs⟩
      have hb := hone (f s) (Finset.mem_image.mpr ⟨s, hes, rfl⟩)
      rwa [hfc s hes] at hb
  · right
    intro s hs
    by_cases he : s = {i}
    · exact Or.inl he
    · have hes : s ∈ A.erase {i} := Finset.mem_erase.mpr ⟨he, hs⟩
      have hb := htwo (f s) (Finset.mem_image.mpr ⟨s, hes, rfl⟩)
      rw [hfc s hes] at hb
      exact Or.inr ⟨hb, hnot s hes⟩

end SymmetricSubgroupAsymptotics
