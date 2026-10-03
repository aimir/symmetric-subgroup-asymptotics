import SymmetricSubgroupAsymptotics.ActualWreathCompressionOrder

/-!
# Logarithmic chief-factor budgets for actual wreath compression

The elementary prime dimensions and the local simple factors split the
base-two logarithm of the component order exactly.  This gives one common
budget for all finite constants in the affine tower.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Base-two logarithmic order spent on elementary chief factors. -/
noncomputable def elementaryLogBudget :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact Module.finrank (ZMod C.p) C.V * Real.logb 2 C.p +
        elementaryLogBudget next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact elementaryLogBudget next

/-- Base-two logarithmic order spent on local nonabelian chief factors. -/
noncomputable def semisimpleLogBudget :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact semisimpleLogBudget next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) +
        semisimpleLogBudget next

private theorem logb_two_prod_nat
    {ι : Type} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) :
    Real.logb 2 ((∏ i ∈ s, f i : ℕ) : ℝ) =
      ∑ i ∈ s, Real.logb 2 (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : (f a : ℝ) ≠ 0 := by
        exact_mod_cast (hf a (Finset.mem_insert_self _ _)).ne'
      have hfs : (((∏ i ∈ s, f i : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast
          (Finset.prod_pos fun i hi =>
            hf i (Finset.mem_insert_of_mem hi)).ne'
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.cast_mul,
        Real.logb_mul hfa hfs]
      rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem logb_localFactorOrderProduct :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      Real.logb 2 T.localFactorOrderProduct =
        T.elementaryLogBudget + T.semisimpleLogBudget
  | _, .terminal _ _ => by
      simp [localFactorOrderProduct, elementaryLogBudget,
        semisimpleLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hp0 : (C.p : ℝ) ≠ 0 := by exact_mod_cast C.p_prime.pos.ne'
      have hnext0 : (next.localFactorOrderProduct : ℝ) ≠ 0 := by
        have hn : next.localFactorOrderProduct ≠ 0 := Nat.ne_of_gt (by
          rw [next.localFactorOrderProduct_eq_card]
          exact Nat.card_pos)
        exact_mod_cast hn
      rw [localFactorOrderProduct, Nat.cast_mul, Nat.cast_pow,
        Real.logb_mul (pow_ne_zero _ hp0) hnext0, Real.logb_pow,
        logb_localFactorOrderProduct next]
      simp only [elementaryLogBudget, semisimpleLogBudget]
      ring
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hprod0 : (((∏ i : C.ι, Nat.card (C.factor i) : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Finset.prod_pos fun i _ => Nat.card_pos).ne'
      have hnext0 : (next.localFactorOrderProduct : ℝ) ≠ 0 := by
        have hn : next.localFactorOrderProduct ≠ 0 := Nat.ne_of_gt (by
          rw [next.localFactorOrderProduct_eq_card]
          exact Nat.card_pos)
        exact_mod_cast hn
      rw [localFactorOrderProduct, Nat.cast_mul,
        Real.logb_mul hprod0 hnext0, logb_localFactorOrderProduct next]
      have hprod := logb_two_prod_nat Finset.univ
        (fun i : C.ι => Nat.card (C.factor i))
        (fun i _ => Nat.card_pos)
      rw [show Real.logb 2
          ((∏ i : C.ι, Nat.card (C.factor i) : ℕ) : ℝ) =
          ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i) : ℝ) by
        simpa using hprod]
      simp only [elementaryLogBudget, semisimpleLogBudget]
      ring

/-- The two retained budgets partition the exact logarithmic order of the
original local component. -/
theorem elementaryLogBudget_add_semisimpleLogBudget_eq_card
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S) :
    T.elementaryLogBudget + T.semisimpleLogBudget =
      Real.logb 2 (Nat.card S.D) := by
  rw [← T.localFactorOrderProduct_eq_card]
  exact (logb_localFactorOrderProduct T).symm

theorem elementaryLogBudget_nonneg :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) → 0 ≤ T.elementaryLogBudget
  | _, .terminal _ _ => by simp [elementaryLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simp only [elementaryLogBudget]
      exact add_nonneg (mul_nonneg (by positivity)
        (Real.logb_nonneg (by norm_num) (by exact_mod_cast C.p_prime.one_lt.le)))
        (elementaryLogBudget_nonneg next)
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [elementaryLogBudget] using elementaryLogBudget_nonneg next

theorem semisimpleLogBudget_nonneg :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) → 0 ≤ T.semisimpleLogBudget
  | _, .terminal _ _ => by simp [semisimpleLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [semisimpleLogBudget] using semisimpleLogBudget_nonneg next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simp only [semisimpleLogBudget]
      exact add_nonneg (Finset.sum_nonneg fun i _ =>
        Real.logb_nonneg (by norm_num)
          (by exact_mod_cast Nat.card_pos (α := C.factor i)))
        (semisimpleLogBudget_nonneg next)

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
