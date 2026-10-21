import SymmetricSubgroupAsymptotics.BinaryFourQuadraticAdjacentConsumer
import SymmetricSubgroupAsymptotics.BinaryFourQuadraticDisjointConsumer
import SymmetricSubgroupAsymptotics.BinaryBooleanFourLargeQuadraticSet
import SymmetricSubgroupAsymptotics.BinaryGenericPairLeadingGeneratorBound

/-! Any four actual quadratic leading shears give two-layer width at
most seven. Only the two abstract orbits of a missing quadratic pair are
used; no invariant-module family or point action is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFourQuadraticPairWidth
open BinaryElementaryPairMonomialWidth BinaryBooleanFourPolynomialCoordinates

def Allowed (Q : Finset (Fin 16)) (s : Finset (Fin 4)) : Prop :=
  s.card ≤ 1 ∨ ∃ a ∈ Q, s = support a

private theorem quadratic_pair_intersection : ∀ m n : Fin 16,
    (support m).card = 2 → (support n).card = 2 → m ≠ n →
      (support m ∩ support n).card = 0 ∨ (support m ∩ support n).card = 1 := by decide

theorem antichain_card_le_seven (Q : Finset (Fin 16))
    (hQ : ∀ a ∈ Q, (support a).card = 2) (hcard : 4 ≤ Q.card)
    (s : Finset Monomial)
    (hs : IsAntichain (BinaryGenericPairLeadingGeneratorBound.Raises (Allowed Q)) (s : Set Monomial)) :
    s.card ≤ 7 := by
  classical
  obtain ⟨T, hTQ, hTc⟩ := Finset.exists_subset_card_eq hcard
  have hT : T ⊆ quadraticMasks := by
    intro a ha
    exact (mem_quadraticMasks_iff a).mpr (hQ a (hTQ ha))
  let R := quadraticMasks \ T
  have hRc : R.card = 2 := by
    rw [Finset.card_sdiff_of_subset hT, hTc]
    have hc : quadraticMasks.card = 6 := by decide
    rw [hc]
  obtain ⟨m, n, hmn, hR⟩ := Finset.card_eq_two.mp hRc
  have hmR : m ∈ R := by rw [hR]; exact Finset.mem_insert_self _ _
  have hnR : n ∈ R := by rw [hR]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hm : (support m).card = 2 :=
    (mem_quadraticMasks_iff m).mp (Finset.mem_sdiff.mp hmR).1
  have hn : (support n).card = 2 :=
    (mem_quadraticMasks_iff n).mp (Finset.mem_sdiff.mp hnR).1
  have hcover (a : Fin 16) (ha : a ∈ quadraticMasks) (ham : a ≠ m) (han : a ≠ n) : a ∈ Q := by
    apply hTQ
    by_contra hnot
    have har : a ∈ R := Finset.mem_sdiff.mpr ⟨ha, hnot⟩
    rw [hR] at har
    rcases Finset.mem_insert.mp har with he | he
    · exact ham he
    · exact han (Finset.mem_singleton.mp he)
  let Small : Finset (Fin 4) → Prop := fun t =>
    t.card ≤ 1 ∨ (t.card = 2 ∧ t ≠ support m ∧ t ≠ support n)
  have hAllowed (t : Finset (Fin 4)) (ht : Small t) : Allowed Q t := by
    rcases ht with ht | ⟨hc, htm, htn⟩
    · exact Or.inl ht
    · let a := BinaryBooleanFourSupportRelabel.supportEquiv.symm t
      have ha : support a = t := BinaryBooleanFourSupportRelabel.supportEquiv.apply_symm_apply t
      have haq : a ∈ quadraticMasks := (mem_quadraticMasks_iff a).mpr (ha.symm ▸ hc)
      have ham : a ≠ m := fun he => htm (ha.symm.trans (congrArg support he))
      have han : a ≠ n := fun he => htn (ha.symm.trans (congrArg support he))
      exact Or.inr ⟨a, hcover a haq ham han, ha.symm⟩
  have hrel (a b : Monomial) : BinaryGenericPairLeadingGeneratorBound.Raises Small a b →
      BinaryGenericPairLeadingGeneratorBound.Raises (Allowed Q) a b := by
    rcases a with ⟨l, a⟩
    rcases b with ⟨r, b⟩
    cases l <;> cases r <;> intro hab
    all_goals first | exact hab | exact hAllowed _ hab
  have hsmall : IsAntichain (BinaryGenericPairLeadingGeneratorBound.Raises Small) (s : Set Monomial) := by
    intro a ha b hb hne hab
    exact hs ha hb hne (hrel a b hab)
  rcases quadratic_pair_intersection m n hm hn hmn with he | he
  · exact BinaryFourQuadraticDisjointConsumer.antichain_card_le_seven_of_disjoint m n hm hn he s hsmall
  · exact BinaryFourQuadraticAdjacentConsumer.antichain_card_le_seven_of_adjacent m n hm hn he s hsmall

end SymmetricSubgroupAsymptotics.BinaryFourQuadraticPairWidth
