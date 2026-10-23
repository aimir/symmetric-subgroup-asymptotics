import SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators

/-! All seven integral coefficients of conjugation by a literal cubic
root polynomial. Degree three and the higher coefficients are retained;
vanishing on a particular Lie image must be proved separately. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators
open scoped BigOperators
variable (R : Type*) [CommRing R] {B : Type*} [Ring B] [Algebra R B]

def operator (e d c : B) (k : ℕ) : Module.End R B :=
  if k=0 then 1 else if k=1 then
    LinearMap.mulLeft R e-LinearMap.mulRight R e else if k=2 then
    LinearMap.mulLeft R d+LinearMap.mulRight R d-
      (LinearMap.mulRight R e).comp (LinearMap.mulLeft R e) else if k=3 then
    LinearMap.mulLeft R c-LinearMap.mulRight R c+
      (LinearMap.mulRight R d).comp (LinearMap.mulLeft R e)-
      (LinearMap.mulRight R e).comp (LinearMap.mulLeft R d) else if k=4 then
    (LinearMap.mulRight R d).comp (LinearMap.mulLeft R d)-
      (LinearMap.mulRight R c).comp (LinearMap.mulLeft R e)-
      (LinearMap.mulRight R e).comp (LinearMap.mulLeft R c) else if k=5 then
    (LinearMap.mulRight R d).comp (LinearMap.mulLeft R c)-
      (LinearMap.mulRight R c).comp (LinearMap.mulLeft R d) else if k=6 then
    -((LinearMap.mulRight R c).comp (LinearMap.mulLeft R c)) else 0

@[simp] theorem operator_zero (e d c x : B) : operator R e d c 0 x=x := by simp [operator]
@[simp] theorem operator_one (e d c x : B) : operator R e d c 1 x=e*x-x*e := by simp [operator]
@[simp] theorem operator_two (e d c x : B) : operator R e d c 2 x=d*x+x*d-e*x*e := by simp [operator]
@[simp] theorem operator_three (e d c x : B) :
    operator R e d c 3 x=c*x-x*c+e*x*d-d*x*e := by simp [operator]
@[simp] theorem operator_four (e d c x : B) :
    operator R e d c 4 x=d*x*d-e*x*c-c*x*e := by simp [operator]
@[simp] theorem operator_five (e d c x : B) : operator R e d c 5 x=c*x*d-d*x*c := by simp [operator]
@[simp] theorem operator_six (e d c x : B) : operator R e d c 6 x= -(c*x*c) := by simp [operator]

theorem operator_large (e d c x : B) (k : ℕ) (hk : 7≤k) : operator R e d c k x=0 := by
  simp [operator,show k≠0 by omega,show k≠1 by omega,show k≠2 by omega,
    show k≠3 by omega,show k≠4 by omega,show k≠5 by omega,show k≠6 by omega]

theorem operator_changeScalars (S : Type*) [CommRing S] [Algebra S B]
    (e d c x : B) (k : ℕ) : operator R e d c k x=operator S e d c k x := by
  unfold operator
  split_ifs <;> rfl

theorem map_operator {C : Type*} [Ring C] [Algebra R C]
    (f : B→+*C) (e d c x : B) (k : ℕ) :
    f (operator R e d c k x)=operator R (f e) (f d) (f c) k (f x) := by
  by_cases hk : 7≤k
  · rw [operator_large R e d c x k hk,map_zero,
      operator_large R (f e) (f d) (f c) (f x) k hk]
  · have hlt : k<7 := by omega
    interval_cases k <;> simp only [operator_zero,operator_one,operator_two,operator_three,
      operator_four,operator_five,operator_six,map_sub,map_mul,map_add,map_neg]

def exponential (e d c : B) (t : R) : B := 1+t • e+t^2 • d+t^3 • c

theorem operator_sum_eq_conjugation (t : R) (e d c x : B) :
    (∑k∈Finset.range 7,t^k • operator R e d c k x)=
      exponential R e d c t*x*exponential R e d c (-t) := by
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,operator_zero,operator_one,
    operator_two,operator_three,operator_four,operator_five,operator_six,pow_zero,pow_one,one_smul]
  simp only [exponential,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
    mul_smul_comm,smul_smul,neg_smul,mul_neg,neg_mul,neg_neg,
    smul_add,smul_sub,smul_neg,pow_succ,pow_zero,mul_one,mul_assoc]
  abel

end SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators
