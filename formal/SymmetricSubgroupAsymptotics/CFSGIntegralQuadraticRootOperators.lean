import SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators
import Mathlib.Tactic.Abel

/-! Integral coefficients of conjugation by a quadratic root exponential.
The fourth coefficient is retained on arbitrary matrices. Its vanishing
on a particular original Lie image must be proved separately. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators
open scoped BigOperators
variable (R : Type*) [CommRing R] {B : Type*} [Ring B] [Algebra R B]

def operator (e d : B) (k : ℕ) : Module.End R B :=
  if k=0 then 1 else if k=1 then
    LinearMap.mulLeft R e - LinearMap.mulRight R e else if k=2 then
    LinearMap.mulLeft R d + LinearMap.mulRight R d -
      (LinearMap.mulRight R e).comp (LinearMap.mulLeft R e) else if k=3 then
    (LinearMap.mulRight R d).comp (LinearMap.mulLeft R e) -
      (LinearMap.mulRight R e).comp (LinearMap.mulLeft R d) else if k=4 then
    (LinearMap.mulRight R d).comp (LinearMap.mulLeft R d) else 0

@[simp] theorem operator_zero (e d x : B) : operator R e d 0 x=x := by simp [operator]
@[simp] theorem operator_one (e d x : B) : operator R e d 1 x=e*x-x*e := by simp [operator]
@[simp] theorem operator_two (e d x : B) : operator R e d 2 x=d*x+x*d-e*x*e := by simp [operator]
@[simp] theorem operator_three (e d x : B) : operator R e d 3 x=e*x*d-d*x*e := by simp [operator]
@[simp] theorem operator_four (e d x : B) : operator R e d 4 x=d*x*d := by simp [operator]

theorem operator_large (e d x : B) (k : ℕ) (hk : 5≤k) : operator R e d k x=0 := by
  simp [operator,show k≠0 by omega,show k≠1 by omega,show k≠2 by omega,
    show k≠3 by omega,show k≠4 by omega]

theorem operator_changeScalars (S : Type*) [CommRing S] [Algebra S B]
    (e d x : B) (k : ℕ) : operator R e d k x=operator S e d k x := by
  unfold operator
  split_ifs <;> rfl

theorem map_operator {C : Type*} [Ring C] [Algebra R C]
    (f : B→+*C) (e d x : B) (k : ℕ) :
    f (operator R e d k x)=operator R (f e) (f d) k (f x) := by
  by_cases hk : 5≤k
  · rw [operator_large R e d x k hk,map_zero,
      operator_large R (f e) (f d) (f x) k hk]
  · have hlt : k<5 := by omega
    interval_cases k <;> simp only [operator_zero,operator_one,operator_two,
      operator_three,operator_four,map_sub,map_mul,map_add]

def exponential (e d : B) (t : R) : B := 1+t • e+t^2 • d

theorem polynomial_eq_conjugation (t : R) (e d x : B) :
    x+t • (e*x-x*e)+t^2 • (d*x+x*d-e*x*e)+
      t^3 • (e*x*d-d*x*e)+t^4 • (d*x*d)=
      exponential R e d t*x*exponential R e d (-t) := by
  simp only [exponential,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
    mul_smul_comm,smul_smul,neg_smul,mul_neg,neg_mul,neg_neg,
    smul_add,smul_sub,smul_neg,pow_succ,pow_zero,mul_one,mul_assoc]
  abel

theorem operator_sum_eq_conjugation (t : R) (e d x : B) :
    (∑k∈Finset.range 5,t^k • operator R e d k x)=
      exponential R e d t*x*exponential R e d (-t) := by
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    operator_zero,operator_one,operator_two,operator_three,operator_four,
    pow_zero,pow_one,one_smul]
  exact polynomial_eq_conjugation R t e d x

theorem truncated_sum_eq_conjugation (t : R) (e d x : B) (hx : d*x*d=0) :
    (∑k∈Finset.range 4,t^k • operator R e d k x)=
      exponential R e d t*x*exponential R e d (-t) := by
  have hh := operator_sum_eq_conjugation R t e d x
  simpa only [Finset.sum_range_succ,operator_four,hx,smul_zero,add_zero] using hh

end SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators
