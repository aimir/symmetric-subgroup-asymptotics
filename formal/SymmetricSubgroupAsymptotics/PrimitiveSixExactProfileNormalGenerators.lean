import SymmetricSubgroupAsymptotics.PrimitiveBoundedCataloguePublishedLocator
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! The existing exact primitive socle profile and existing published bounded
catalogue suffice for normal generation in degree six. The index inequality
forces one socle factor; the actual degree-six receipt has socle quotient
order at most two. Thus all original normal subgroups form a chain.
No degree-six group-isomorphism classification is an additional input. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators

theorem six_not_two_power (d : ℕ) : 6 ≠ 2 ^ d := by
  intro h
  by_cases hd : d < 3
  · interval_cases d <;> norm_num at h
  · have h3 : 3 ≤ d := by omega
    have h8 : (8 : ℕ) ≤ 2 ^ d := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) h3
    omega

/-- Only the already stored receipt rows are inspected; their cardinalities
still cross exactly the existing published catalogue boundary. -/
theorem six_receipt_outer_le_two : ∀ i : Fin 116,
    (primitiveBoundedIndexRow i).degree = 6 →
      (primitiveBoundedIndexRow i).outerOrder ≤ 2 := by
  decide +kernel

/-- The same existing degree-six rows have group order divisible by five. -/
theorem six_receipt_five_dvd_groupOrder : ∀ i : Fin 116,
    (primitiveBoundedIndexRow i).degree = 6 →
      5 ∣ (primitiveBoundedIndexRow i).groupOrder := by
  decide +kernel

theorem subgroup_total_of_card_le_two {Q : Type} [Group Q] [Finite Q]
    (hcard : Nat.card Q ≤ 2) (A B : Subgroup Q) : A ≤ B ∨ B ≤ A := by
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hcases : Nat.card Q = 1 ∨ Nat.card Q = 2 := by omega
  rcases hcases with hone | htwo
  · letI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hone).1
    exact Or.inl (by intro x hx; simpa only [Subsingleton.elim x 1] using B.one_mem)
  · letI : Fact (Nat.card Q).Prime := ⟨by rw [htwo]; decide⟩
    rcases A.eq_bot_or_eq_top_of_prime_card with hA | hA
    · exact Or.inl (hA ▸ bot_le)
    · exact Or.inr (hA ▸ le_top)

/-- Unique minimal normal containment and a quotient of order at most two
make the whole original normal lattice a chain. -/
theorem normal_total_of_unique_minimal_small_quotient
    {G : Type} [Group G] [Finite G] (E : Subgroup G) [E.Normal]
    (hmin : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → E ≤ N)
    (hcard : Nat.card (G ⧸ E) ≤ 2)
    (A B : Subgroup G) (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  by_cases hAb : A = ⊥
  · exact Or.inl (hAb ▸ bot_le)
  by_cases hBb : B = ⊥
  · exact Or.inr (hBb ▸ bot_le)
  let pi : G →* G ⧸ E := QuotientGroup.mk' E
  have hEA : pi.ker ≤ A := by simpa only [pi,QuotientGroup.ker_mk'] using hmin A hA hAb
  have hEB : pi.ker ≤ B := by simpa only [pi,QuotientGroup.ker_mk'] using hmin B hB hBb
  have hAc : (A.map pi).comap pi = A := Subgroup.comap_map_eq_self hEA
  have hBc : (B.map pi).comap pi = B := Subgroup.comap_map_eq_self hEB
  rcases subgroup_total_of_card_le_two hcard (A.map pi) (B.map pi) with h | h
  · exact Or.inl (by rw [← hAc,← hBc]; exact Subgroup.comap_mono h)
  · exact Or.inr (by rw [← hAc,← hBc]; exact Subgroup.comap_mono h)

variable {L : Type} [Group L] [Finite L] [MulAction L (Fin 6)]
    [FaithfulSMul L (Fin 6)] [MulAction.IsPreprimitive L (Fin 6)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile L 6)
    (catalogue : PublishedBoundedPrimitiveCatalogueClassification)

theorem factorCount_eq_one : D.profile.factorCount = 1 := by
  have hp := D.profile.factorCount_pos
  have h5 := D.profile.leastIndex_five_le
  have hl := D.profile.primitive_index_lower
  by_contra hn
  have h2 : 2 ≤ D.profile.factorCount := by omega
  have h25 : 25 ≤ D.profile.leastIndex ^ D.profile.factorCount := by
    calc
      25 = (5 : ℕ) ^ 2 := rfl
      _ ≤ D.profile.leastIndex ^ 2 := Nat.pow_le_pow_left h5 2
      _ ≤ D.profile.leastIndex ^ D.profile.factorCount :=
        pow_le_pow_right₀ (by omega : 1 ≤ D.profile.leastIndex) h2
  omega

include catalogue in
theorem socle_quotient_card_le_two : Nat.card (L ⧸ D.profile.E) ≤ 2 := by
  have hone := factorCount_eq_one D
  obtain ⟨M⟩ := catalogue L (Fin 6) D.profile.E D.profile.chart
    (by simp) (by simp) (D.oneFactor_socle_nontrivial hone)
    (D.oneFactor_socle_le hone) (D.factorCount_eq_chart.symm.trans hone)
  exact M.quotientOrder_eq.trans_le
    (six_receipt_outer_le_two M.row (by simpa using M.degree_eq))

include D catalogue in
theorem five_dvd_card : 5 ∣ Nat.card L := by
  have hone := factorCount_eq_one D
  obtain ⟨M⟩ := catalogue L (Fin 6) D.profile.E D.profile.chart
    (by simp) (by simp) (D.oneFactor_socle_nontrivial hone)
    (D.oneFactor_socle_le hone) (D.factorCount_eq_chart.symm.trans hone)
  rw [M.groupOrder_eq]
  exact six_receipt_five_dvd_groupOrder M.row (by simpa using M.degree_eq)

include D catalogue in
theorem normal_total (A B : Subgroup L) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normal_total_of_unique_minimal_small_quotient D.profile.E
    (D.oneFactor_socle_le (factorCount_eq_one D))
    (socle_quotient_card_le_two D catalogue) A B hA hB

include D catalogue in
theorem normal_generating_singletons (N : Subgroup L) (hN : N.Normal) :
    ∃ x : Fin 1 → L, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total (normal_total D catalogue) N hN

end SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators

end
