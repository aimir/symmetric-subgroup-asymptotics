import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawProfile

/-! The sufficient budget is installed on the literal full-socle quotient.
The quotient embedding, original group, action and normal subgroup are not
replaced. These proofs use only the new budget's order-square component
and actual outer-wreath embedding, never the stronger old logarithm. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.sufficient_degree_lower (D : NonaffineData G X)
    (hindex : SufficientSimpleIndexBounds) :
    ∃ ell : ℕ, LeastProperIndex D.Simple ell ∧ 5 ≤ ell ∧
      ell ^ D.factorCount ≤ Nat.card X ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨ho, hb⟩ := hindex D.Simple D.noncommutative ell hell
  exact ⟨ell, hell, hf, primitiveSocle_power_le_degree hf ho (D.degreeForm hell), hb⟩

theorem NonaffineData.oneFactor_sufficient_budget (D : NonaffineData G X)
    (hk : D.factorCount = 1) (hindex : SufficientSimpleIndexBounds) :
    ∃ ell : ℕ, LeastProperIndex D.Simple ell ∧ 5 ≤ ell ∧ ell ≤ Nat.card X ∧
      SufficientOuterOrderBudget ell (Nat.card (G ⧸ finiteGroupSocle G)) := by
  obtain ⟨ell, hell, hf, hd, hb⟩ := D.sufficient_degree_lower hindex
  have he : ell ≤ Nat.card X := by simpa only [hk, pow_one] using hd
  have hw : Nat.card (Wreath (Outer D.Simple) D.factorCount) = Nat.card (Outer D.Simple) := by
    rw [hk]
    exact wreath_one_card (Outer D.Simple)
  have hc : Nat.card (G ⧸ finiteGroupSocle G) ≤ Nat.card (Outer D.Simple) :=
    (Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective).trans_eq hw
  exact ⟨ell, hell, hf, he, hb.mono hc⟩

theorem NonaffineData.degree_five_le_of_sufficient (D : NonaffineData G X)
    (hindex : SufficientSimpleIndexBounds) : 5 ≤ Nat.card X := by
  obtain ⟨ell, _, hf, hd, _⟩ := D.sufficient_degree_lower hindex
  have hp : ell ≤ ell ^ D.factorCount := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ ell)
      (show 1 ≤ D.factorCount by have := D.factorCount_pos; omega))
  omega

theorem NonaffineData.factorCount_one_of_sufficient_degree_lt_twentyFive
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hdegree : Nat.card X < 25) : D.factorCount = 1 := by
  obtain ⟨ell, _, hf, hd, _⟩ := D.sufficient_degree_lower hindex
  by_contra h
  have hk : 2 ≤ D.factorCount := by have := D.factorCount_pos; omega
  have h25 : 25 ≤ ell ^ D.factorCount := calc
    25 = 5 ^ 2 := by decide
    _ ≤ ell ^ 2 := Nat.pow_le_pow_left hf 2
    _ ≤ ell ^ D.factorCount := pow_le_pow_right₀ (by omega : 1 ≤ ell) hk
  omega

theorem NonaffineData.oneFactor_sharp_log_of_sufficient_degree_lt_twentySeven
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (hindex : SufficientSimpleIndexBounds) (hsmall : Nat.card X < 27) :
    ∃ ell : ℕ, LeastProperIndex D.Simple ell ∧ 5 ≤ ell ∧ ell ≤ Nat.card X ∧
      (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤ 3 * Real.logb 2 ell := by
  obtain ⟨ell, he, hf, hd, hb⟩ := D.oneFactor_sufficient_budget hk hindex
  exact ⟨ell, he, hf, hd, hb.log_three_of_small (by omega)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
