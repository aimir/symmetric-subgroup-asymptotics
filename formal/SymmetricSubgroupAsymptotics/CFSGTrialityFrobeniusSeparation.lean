import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
import Mathlib.Algebra.Polynomial.Roots

/-! Independence of the three literal cubic Frobenius parameter
functions. The polynomial has degree at most q^2 < q^3, including q=2;
there is no division by two or three and no trace(1) assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Polynomial
namespace SymmetricSubgroupAsymptotics.CFSGTrialityFrobeniusSeparation
open CFSGSerreOrdinaryTwists

theorem linearized_coefficients_zero (K : Type) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : q^2 < Nat.card K) (a b c : K)
    (h : ∀ t : K, a*t + b*t^q + c*t^(q^2) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite _
  let P : K[X] := Polynomial.monomial 1 a + Polynomial.monomial q b +
    Polynomial.monomial (q^2) c
  have hqq : q < q^2 := by nlinarith
  have hdeg : P.natDegree ≤ q^2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_monomial_le a).trans (by nlinarith)
      · exact (Polynomial.natDegree_monomial_le b).trans hqq.le
    · exact Polynomial.natDegree_monomial_le c
  have hev (t : K) : P.eval t = 0 := by
    simpa only [P,Polynomial.eval_add,Polynomial.eval_monomial,pow_one] using h t
  have hzero : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P Function.injective_id hev (by
      simpa only [Nat.card_eq_fintype_card] using hdeg.trans_lt hcard)
  have hq1 : q ≠ 1 := by omega
  have hq21 : q^2 ≠ 1 := by nlinarith
  have hq2q : q^2 ≠ q := ne_of_gt hqq
  have h1 := congrArg (fun R : K[X] => R.coeff 1) hzero
  have h2 := congrArg (fun R : K[X] => R.coeff q) hzero
  have h3 := congrArg (fun R : K[X] => R.coeff (q^2)) hzero
  refine ⟨?_,?_,?_⟩
  · simpa [P,Polynomial.coeff_monomial,hq1,hq21,hq2q,Ne.symm hq1,Ne.symm hq21,Ne.symm hq2q] using h1
  · simpa [P,Polynomial.coeff_monomial,hq1,hq21,hq2q,Ne.symm hq1,Ne.symm hq21,Ne.symm hq2q] using h2
  · simpa [P,Polynomial.coeff_monomial,hq1,hq21,hq2q,Ne.symm hq1,Ne.symm hq21,Ne.symm hq2q] using h3

theorem actual_frobenius_coefficients_zero (q : CFSG.PrimePower)
    (a b c : q.Extension 3)
    (h : ∀ t : q.Extension 3, a*t + b*definingFieldAutomorphism q 3 t +
      c*definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  apply linearized_coefficients_zero (q.Extension 3) q.order hq
  · rw [CFSGTrialityTripleFixedRoots.extension_three_card]
    exact pow_lt_pow_right₀ (by omega : 1 < q.order) (by decide : (2 : ℕ) < 3)
  · intro t
    simpa only [definingFieldAutomorphism_apply,←pow_mul,pow_two] using h t

end SymmetricSubgroupAsymptotics.CFSGTrialityFrobeniusSeparation
