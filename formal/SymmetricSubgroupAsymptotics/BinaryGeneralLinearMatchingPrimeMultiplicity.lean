import SymmetricSubgroupAsymptotics.BinaryGeneralLinearTotalPrimeMultiplicity

/-! A uniform bound for the matching-characteristic coefficient in the
actual binary GL order, including the literal translation head. It uses
only the exact defining valuation and the proved total multiplicity,
not a catalogue of possible complement groups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearMatchingPrimeMultiplicity

private theorem factorization_le_cardFactors (M p : ℕ) :
    M.factorization p ≤ ArithmeticFunction.cardFactors M := by
  by_cases hp : M.factorization p = 0
  · rw [hp]
    exact Nat.zero_le _
  · have hmem := Finsupp.mem_support_iff.mpr hp
    have hh := Finset.single_le_sum
      (fun i (_ : i ∈ M.factorization.support) => Nat.zero_le (M.factorization i)) hmem
    simpa only [ArithmeticFunction.cardFactors_eq_sum_factorization,Finsupp.sum] using hh

theorem pair_factorizations_le_cardFactors (M p q : ℕ) (hpq : p ≠ q) :
    M.factorization p + M.factorization q ≤ ArithmeticFunction.cardFactors M := by
  by_cases hp : M.factorization p = 0
  · simpa only [hp,zero_add] using factorization_le_cardFactors M q
  by_cases hq : M.factorization q = 0
  · simpa only [hq,add_zero] using factorization_le_cardFactors M p
  have hsub : ({p,q} : Finset ℕ) ⊆ M.factorization.support := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finsupp.mem_support_iff.mpr hp
    · exact Finsupp.mem_support_iff.mpr hq
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i (_ : i ∈ M.factorization.support) (_ : i ∉ ({p,q} : Finset ℕ)) =>
      Nat.zero_le (M.factorization i))
  simpa only [Finset.sum_pair hpq,ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum] using hh

theorem GL_factorization_le_triangle (d q : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).factorization q ≤
      d*(d-1)/2 := by
  by_cases hq : q = 2
  · subst q
    exact (PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization
      2 d Nat.prime_two).le
  · have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q 2 hq
    rw [PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization
      2 d Nat.prime_two] at hh
    have htotal := BinaryGeneralLinearTotalPrimeMultiplicity.GL_cardFactors_le d
    have heven := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self d)
    omega

def matchingMultiplicity (d q : ℕ) : ℕ :=
  (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).factorization q +
    if q = 2 then d else 0

theorem matchingMultiplicity_le_triangle (d q : ℕ) :
    matchingMultiplicity d q ≤ d+d*(d-1)/2 := by
  have hh := GL_factorization_le_triangle d q
  unfold matchingMultiplicity
  split_ifs <;> omega

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearMatchingPrimeMultiplicity
