import SymmetricSubgroupAsymptotics.CFSGProjectivePolynomialCount
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSignedForm

/-! The literal signed unitary norm as a homogeneous polynomial of
degree q+1 over the actual quadratic field. Nonvanishing in dimension
four uses a genuine non-Frobenius-fixed scalar, including q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
open MvPolynomial CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

def signedNorm (q : CFSG.PrimePower) (r : ℕ) (v : Fin (r + 1) → q.Extension 2) :
    q.Extension 2 :=
  ∑ i, signWeight (q.Extension 2) r i * definingFieldAutomorphism q 2 (v i) * v i.rev

def normPolynomial (q : CFSG.PrimePower) (r : ℕ) :
    MvPolynomial (Fin (r + 1)) (q.Extension 2) :=
  ∑ i, C (signWeight (q.Extension 2) r i) * X i ^ q.order * X i.rev

theorem eval_normPolynomial (q : CFSG.PrimePower) (r : ℕ)
    (v : Fin (r + 1) → q.Extension 2) :
    MvPolynomial.eval v (normPolynomial q r) = signedNorm q r v := by
  simp only [normPolynomial, map_sum, map_mul, map_pow, eval_C, eval_X]
  rfl

theorem signedNorm_smul (q : CFSG.PrimePower) (r : ℕ) (a : q.Extension 2)
    (v : Fin (r + 1) → q.Extension 2) :
    signedNorm q r (a • v) =
      (definingFieldAutomorphism q 2 a * a) * signedNorm q r v := by
  unfold signedNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem normPolynomial_degree_le (q : CFSG.PrimePower) (r : ℕ) :
    (normPolynomial q r).totalDegree ≤ q.order + 1 := by
  classical
  have hterm (i : Fin (r + 1)) :
      (C (signWeight (q.Extension 2) r i) * X i ^ q.order * X i.rev :
        MvPolynomial (Fin (r + 1)) (q.Extension 2)).totalDegree ≤ q.order + 1 := by
    apply (totalDegree_mul _ _).trans
    have hc := totalDegree_mul (C (signWeight (q.Extension 2) r i)) (X i ^ q.order)
    simpa only [totalDegree_C, totalDegree_X_pow, totalDegree_X, zero_add] using
      Nat.add_le_add_right hc 1
  have hall (S : Finset (Fin (r + 1))) :
      (∑ i ∈ S, C (signWeight (q.Extension 2) r i) * X i ^ q.order * X i.rev :
        MvPolynomial (Fin (r + 1)) (q.Extension 2)).totalDegree ≤ q.order + 1 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (totalDegree_add _ _).trans (max_le (hterm i) ih)
  exact hall Finset.univ

theorem normPolynomial_rank_three_ne_zero (q : CFSG.PrimePower) :
    normPolynomial q 3 ≠ 0 := by
  obtain ⟨t, ht⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  have hv : signedNorm q 3 ![1, 0, 0, t] = t - definingFieldAutomorphism q 2 t := by
    norm_num [signedNorm, Fin.sum_univ_succ, signWeight, Fin.rev, sub_eq_add_neg]
  intro hz
  have he : signedNorm q 3 ![1, 0, 0, t] = 0 := by
    rw [← eval_normPolynomial, hz]
    exact map_zero _
  exact ht (sub_eq_zero.mp (hv.symm.trans he)).symm

end SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
