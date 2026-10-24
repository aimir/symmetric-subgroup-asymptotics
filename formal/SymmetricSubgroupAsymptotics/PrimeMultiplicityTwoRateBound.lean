import SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget

/-! Separate the actual exponent of one characteristic from all other
prime multiplicities in the SAME local order. No independent order
charges or simple-generation assumption is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimeMultiplicityTwoRateBound
open ActualWreathChiefWeightedPrimeBudget

theorem weightedOrder_two_rates (M q : ℕ) (primary other : ℝ) :
    weightedOrder (fun p => if p = q then primary else other) M =
      (M.factorization q : ℝ)*primary +
        ((ArithmeticFunction.cardFactors M : ℝ)-(M.factorization q : ℝ))*other := by
  have hsplit (p : ℕ) :
      (M.factorization p : ℝ)*(if p = q then primary else other) =
        (M.factorization p : ℝ)*other +
          (if p = q then (M.factorization p : ℝ)*(primary-other) else 0) := by
    split_ifs <;> ring
  have hsingle :
      (∑ p ∈ M.factorization.support,
        if p = q then (M.factorization p : ℝ)*(primary-other) else 0) =
          (M.factorization q : ℝ)*(primary-other) := by
    calc
      _ = (if q = q then (M.factorization q : ℝ)*(primary-other) else 0) := by
        apply Finset.sum_eq_single q
        · intro p _ hp
          simp only [if_neg hp]
        · intro hq
          have hz : M.factorization q = 0 := by
            by_contra hne
            exact hq (Finsupp.mem_support_iff.mpr hne)
          simp only [hz,Nat.cast_zero,zero_mul,ite_self]
      _ = (M.factorization q : ℝ)*(primary-other) := if_pos rfl
  have htotal : (∑ p ∈ M.factorization.support, (M.factorization p : ℝ)) =
      (ArithmeticFunction.cardFactors M : ℝ) := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    simp only [Finsupp.sum,Nat.cast_sum]
  unfold weightedOrder
  simp only [Finsupp.sum,hsplit,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,htotal,hsingle]
  ring

theorem weightedOrder_le_two_rates (weight : ℕ → ℝ) (M q : ℕ)
    (primary other : ℝ) (hprimary : weight q ≤ primary)
    (hother : ∀ p, p ≠ q → weight p ≤ other) :
    weightedOrder weight M ≤ (M.factorization q : ℝ)*primary +
      ((ArithmeticFunction.cardFactors M : ℝ)-(M.factorization q : ℝ))*other := by
  rw [←weightedOrder_two_rates]
  unfold weightedOrder
  rw [Finsupp.sum,Finsupp.sum]
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ M.factorization p by positivity)
  by_cases hp : p = q
  · simpa only [hp,if_pos rfl] using hprimary
  · simpa only [if_neg hp] using hother p hp

end SymmetricSubgroupAsymptotics.PrimeMultiplicityTwoRateBound
