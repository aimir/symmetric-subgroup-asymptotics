import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! The eight subset-of-three Frobenius monomials are independent on a
field of cardinal q^3, including q=2 and characteristics two and three.
Their exponents are all distinct and at most q^2+q+1<q^3. No division,
trace(1), or identification of an actual group radical is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Polynomial
namespace SymmetricSubgroupAsymptotics.CFSGCubicNormMonomialSeparation

def exponent (q : ℕ) (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => q
  | 3 => q+1
  | 4 => q^2
  | 5 => q^2+1
  | 6 => q^2+q
  | _ => q^2+q+1

theorem exponent_injective (q : ℕ) (hq : 2 ≤ q) : Function.Injective (exponent q) := by
  have hmul : q*2 ≤ q*q := Nat.mul_le_mul_left q hq
  have hgap : q+1 < q^2 := by nlinarith
  have hstrict : StrictMono (exponent q) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> norm_num [exponent] <;> omega
  exact hstrict.injective

theorem exponent_le (q : ℕ) (i : Fin 8) : exponent q i ≤ q^2+q+1 := by
  fin_cases i <;> norm_num [exponent] <;> omega

theorem maximum_lt_cube (q : ℕ) (hq : 2 ≤ q) : q^2+q+1 < q^3 := by
  have htwo := Nat.mul_le_mul_left q hq
  have hthree := Nat.mul_le_mul_right (q^2) hq
  nlinarith

def normCurve {K : Type*} [Monoid K] (q : ℕ) (t : K) : Fin 8 → K :=
  fun i=>t^(exponent q i)

theorem coefficients_zero_of_card (K : Type*) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : q^2+q+1 < Nat.card K)
    (c : Fin 8 → K) (h : ∀ t : K, ∑ i : Fin 8,c i*normCurve q t i=0) :
    ∀ i : Fin 8,c i=0 := by
  classical
  letI : Fintype K := Fintype.ofFinite _
  let P : K[X] := ∑ i : Fin 8,Polynomial.monomial (exponent q i) (c i)
  have hdeg : P.natDegree ≤ q^2+q+1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le (c i)).trans (exponent_le q i)
  have hev (t : K) : P.eval t=0 := by
    simpa only [P,Polynomial.eval_finsetSum,Polynomial.eval_monomial,normCurve] using h t
  have hzero : P=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P Function.injective_id hev (by
      simpa only [Nat.card_eq_fintype_card] using hdeg.trans_lt hcard)
  intro i
  have hc := congrArg (fun R : K[X]=>R.coeff (exponent q i)) hzero
  simpa [P,Polynomial.coeff_monomial,(exponent_injective q hq).eq_iff] using hc

theorem coefficients_zero (K : Type*) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K=q^3)
    (c : Fin 8 → K) (h : ∀ t : K, ∑ i : Fin 8,c i*normCurve q t i=0) :
    ∀ i : Fin 8,c i=0 := by
  apply coefficients_zero_of_card K q hq _ c h
  rw [hcard]
  exact maximum_lt_cube q hq

end SymmetricSubgroupAsymptotics.CFSGCubicNormMonomialSeparation
