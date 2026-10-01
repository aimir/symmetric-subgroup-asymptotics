import SymmetricSubgroupAsymptotics.TernaryHighImprimitiveDegrees
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PermutationChiefWeight
import Mathlib.Tactic.NormNum

/-!
# The one-third primitive ternary chief weight from published inputs

The three-tenths primitive bound is already stronger than the one-third
bound except in degree nine, which its statement deliberately omits.  In
degree nine the published primitive-group classification has eleven rows.
Their orders are

`36, 72, 72, 72, 144, 216, 432, 504, 1512, |A₉|, |S₉|`.

The first nine rows have ternary order valuation at most three.  The final
two rows have the standard zero-weight chief series.  This file records the
exact degree-nine consequence of the published classification, proves the
finite arithmetic in Lean, and derives the former project-level
`PrimitiveTernaryChiefWeightBound` assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Exact degree-nine slice of the published primitive permutation-group
classification.  Repeated isomorphism classes of order `72` need not be
distinguished by the chief-weight consumer. -/
def PublishedPrimitiveDegreeNineClassification : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    Nat.card X = 9 →
      Nat.card G = 36 ∨ Nat.card G = 72 ∨ Nat.card G = 144 ∨
      Nat.card G = 216 ∨ Nat.card G = 432 ∨ Nat.card G = 504 ∨
      Nat.card G = 1512 ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 9))

private theorem chiefWeight_le_three_of_degreeNine_small_order
    {G : Type} [Group G] [Finite G]
    (hcard : Nat.card G = 36 ∨ Nat.card G = 72 ∨ Nat.card G = 144 ∨
      Nat.card G = 216 ∨ Nat.card G = 432 ∨ Nat.card G = 504 ∨
      Nat.card G = 1512) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ 3 := by
  have h := actualChiefSeriesTernaryWeight_le_order c
  rcases hcard with hcard | hcard | hcard | hcard | hcard | hcard | hcard
  · exact h.trans (by simpa only [hcard] using
      (show ((36 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((72 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((144 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((216 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((432 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((504 : ℕ).factorization 3) ≤ 3 by decide +kernel))
  · exact h.trans (by simpa only [hcard] using
      (show ((1512 : ℕ).factorization 3) ≤ 3 by decide +kernel))

/-- Every published primitive degree-nine row has a chosen chief series of
ternary weight at most three.  Only the order list and the symbolic `A₉`,
`S₉` chief series are used; no generated rank dataset is trusted. -/
theorem primitiveDegreeNine_chiefWeight_le_three
    (h9 : PublishedPrimitiveDegreeNineClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hdegree : Nat.card X = 9) :
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c ≤ 3 := by
  rcases h9 G X hdegree with h36 | h72 | h144 | h216 | h432 | h504 | h1512 |
      he | he
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order (Or.inl h36) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order (Or.inr (Or.inl h72)) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order
        (Or.inr (Or.inr (Or.inl h144))) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order
        (Or.inr (Or.inr (Or.inr (Or.inl h216)))) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h432))))) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h504)))))) _⟩
  · exact ⟨actualChiefSeries G,
      chiefWeight_le_three_of_degreeNine_small_order
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1512)))))) _⟩
  · let e := Classical.choice he
    obtain ⟨c, hc⟩ := alternatingChiefSeries_zero_of_equiv 9 (by omega) e
    exact ⟨c, by omega⟩
  · let e := Classical.choice he
    obtain ⟨c, hc⟩ := symmetricChiefSeries_zero_of_equiv 9 (by omega) e
    exact ⟨c, by omega⟩

/-- The one-third chief-weight hypothesis used by the ternary recurrence is
not an additional research assumption.  It follows from the stronger
three-tenths bound and the published degree-nine classification. -/
theorem primitiveTernaryChiefWeightBound_of_published
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (h9 : PublishedPrimitiveDegreeNineClassification) :
    PrimitiveTernaryChiefWeightBound (fun r => r / 3) := by
  intro G X _ _ _ _ _ _ _
  let r := Nat.card X
  by_cases hr9 : r = 9
  · simpa only [r, hr9] using
      (primitiveDegreeNine_chiefWeight_le_three h9 G X (by simpa only [r] using hr9))
  by_cases hr4 : 4 ≤ r
  · let c := actualChiefSeries G
    have hw : 10 * actualChiefSeriesTernaryWeight c ≤ 3 * r :=
      hWeight G X (by simpa only [r] using hr4) (by simpa only [r] using hr9) c
    refine ⟨c, (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mpr ?_⟩
    omega
  · let e : X ≃ Fin r := Finite.equivFin X
    let P := labelledActionImage (A := G) e
    let cP := actualChiefSeries P
    let c := faithfulLabelledActionChiefSeries e cP
    have hr : 2 ≤ r := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hcP : actualChiefSeriesTernaryWeight cP ≤ r / 3 := by
      by_cases hr2 : r ≤ 2
      · have hz := permutationChiefWeight_eq_zero_of_card_le_two P cP (by
          simpa only [Nat.card_fin] using hr2)
        omega
      · have ho := permutationChiefWeight_le_one_of_card_le_five P cP (by
          simp only [Nat.card_fin]
          omega)
        omega
    exact ⟨c, by
      rw [show actualChiefSeriesTernaryWeight c =
          actualChiefSeriesTernaryWeight cP from
        faithfulLabelledActionChiefSeries_weight e cP]
      exact hcP⟩

end SymmetricSubgroupAsymptotics

end
