import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivatives

/-! Five actual quadratic leading supports omit at most one quadratic.
Every variable remains covered by one of those actual supports. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

def quadraticMasks : Finset (Fin 16) := {3, 5, 6, 9, 10, 12}

theorem mem_quadraticMasks_iff : ∀ a : Fin 16,
    a ∈ quadraticMasks ↔ (support a).card = 2 := by decide

theorem five_quadratic_masks_cover_except_one (Q : Finset (Fin 16))
    (hQ : ∀ a ∈ Q, (support a).card = 2) (hcard : 5 ≤ Q.card) :
    ∃ m ∈ quadraticMasks, ∀ a ∈ quadraticMasks, a ≠ m → a ∈ Q := by
  classical
  have hsub : Q ⊆ quadraticMasks := by
    intro a ha
    exact (mem_quadraticMasks_iff a).mpr (hQ a ha)
  by_cases hfull : quadraticMasks ⊆ Q
  · exact ⟨3, by decide, fun a ha _ => hfull ha⟩
  · obtain ⟨m, hm, hmQ⟩ := Finset.not_subset.mp hfull
    have he : Q = quadraticMasks.erase m := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        exact Finset.mem_erase.mpr ⟨fun he => hmQ (he ▸ ha), hsub ha⟩
      · have hc := Finset.card_erase_add_one hm
        have ht : quadraticMasks.card = 6 := by decide
        omega
    refine ⟨m, hm, ?_⟩
    intro a ha ham
    rw [he]
    exact Finset.mem_erase.mpr ⟨ham, ha⟩

private theorem variable_covered_except_one_quadratic : ∀ m ∈ quadraticMasks,
    ∀ i : Fin 4, ∃ a ∈ quadraticMasks, a ≠ m ∧ i ∈ support a := by decide

theorem every_variable_covered_by_five_quadratics (Q : Finset (Fin 16))
    (hQ : ∀ a ∈ Q, (support a).card = 2) (hcard : 5 ≤ Q.card)
    (i : Fin 4) : ∃ a ∈ Q, i ∈ support a := by
  obtain ⟨m, hm, hcov⟩ := five_quadratic_masks_cover_except_one Q hQ hcard
  obtain ⟨a, ha, ham, hi⟩ := variable_covered_except_one_quadratic m hm i
  exact ⟨a, hcov a ha ham, hi⟩

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
