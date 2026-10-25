import SymmetricSubgroupAsymptotics.ActualWreathUnitUniformLocalOrderCost

/-! BOTH unconditional induced bounds apply to the SAME actual ordinary
chief trace. Their smaller common rate is at least one, so it also pays
actual internal nonabelian simple-factor ranks by genuine prime multiplicity.
No source generator estimate or numerical fitting inequality is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate
open ActualWreathCharacteristicChiefProfile ActualWreathChiefWeightedPrimeBudget

/-- Retain the better of half degree and the proved constant-one log bound. -/
def rate (t : ℕ) : ℝ := min ((t : ℝ)/2) ((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)))

theorem one_le_rate (t : ℕ) (ht : 2 ≤ t) : 1 ≤ rate t := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 < Real.logb 2 (t : ℝ) :=
    Real.logb_pos (by norm_num) (by linarith only [htR])
  have hs : 0 < Real.sqrt (Real.logb 2 (t : ℝ)) := Real.sqrt_pos.mpr hL
  have hsle : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨by linarith only [htR],
      LargeOrbitGeneratorNumerics.logb_le_square htR⟩
  have hlog : (1 : ℝ) ≤ (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) :=
    (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsle)
  exact le_min (by linarith only [htR]) hlog

theorem elementary_capacity_le_rate {t : ℕ} (c : ElementaryCharge t) (ht : 2 ≤ t) :
    (c.capacity : ℝ) ≤ (c.dimension : ℝ)*rate t := by
  have hh : (c.capacity : ℝ) ≤ (c.dimension : ℝ)*((t : ℝ)/2) := by
    simpa only [mul_div_assoc] using c.half
  have hl : (c.capacity : ℝ) ≤
      (c.dimension : ℝ)*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by
    simpa only [mul_div_assoc] using ElementaryChargeUnitLogarithmic.logarithmic_real c ht
  by_cases h : (t : ℝ)/2 ≤ (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))
  · simpa only [rate,min_eq_left h] using hh
  · simpa only [rate,min_eq_right (le_of_not_ge h)] using hl

private theorem weightedOrder_const (c : ℝ) (M : ℕ) :
    weightedOrder (fun _ => c) M = (ArithmeticFunction.cardFactors M : ℝ)*c := by
  simp only [weightedOrder,ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum,Nat.cast_sum,Finset.sum_mul]

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_cardFactors_mul_rate {i : I} {S : ActualWreathCompressionState Q I}
    {n : ℕ} (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) :
    (n : ℝ) ≤ (ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*rate (Fintype.card I) := by
  have hh := cost_le_weightedOrder h hI (fun _ => rate (Fintype.card I))
    (fun _ => one_le_rate _ hI) (fun c => elementary_capacity_le_rate c hI)
  simpa only [weightedOrder_const] using hh

theorem genRank_le_cardFactors_mul_rate (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    (MarkedC4.genRank S.A : ℝ) ≤
      (ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*rate (Fintype.card I)+
        MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  have hc := cost_le_cardFactors_mul_rate hn hI
  have hsource : (MarkedC4.genRank S.A : ℝ) ≤ (n : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn
  exact hsource.trans (add_le_add hc le_rfl)

/-- A literal trace witness, with the minimum rate proved for that witness. -/
theorem exists_trace_cost_bound (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      (n : ℝ) ≤ (ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*rate (Fintype.card I) ∧
      MarkedC4.genRank S.A ≤ n+MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,cost_le_cardFactors_mul_rate hn hI,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn⟩

end SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate
