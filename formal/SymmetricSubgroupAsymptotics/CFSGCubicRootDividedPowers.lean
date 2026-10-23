import SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators
import SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
import Mathlib.Tactic.NoncommRing

/-! Integral divided-power formulas for a genuine cubic root
exponential. The hypotheses are explicit multiplication identities;
there is no factorial inversion after reducing the integral formulas. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCubicRootDividedPowers
open CFSGIntegralCubicRootOperators
variable {B : Type*} [Ring B] [Algebra ℚ B]
    (e d c : B) (hee : e*e=d+d) (hed : e*d=c+c+c) (hde : d*e=c+c+c)
    (hec : e*c=0) (hce : c*e=0)
include hee hed hde hec hce

theorem ad_operator (k : ℕ) (x : B) :
    ⁅e,operator ℚ e d c k x⁆=((k+1:ℕ):ℚ) • operator ℚ e d c (k+1) x := by
  have eeL (y : B) : e*(e*y)=(d+d)*y := by rw [←mul_assoc,hee]
  have edL (y : B) : e*(d*y)=(c+c+c)*y := by rw [←mul_assoc,hed]
  have deL (y : B) : d*(e*y)=(c+c+c)*y := by rw [←mul_assoc,hde]
  have ecL (y : B) : e*(c*y)=0 := by rw [←mul_assoc,hec,zero_mul]
  have ceL (y : B) : c*(e*y)=0 := by rw [←mul_assoc,hce,zero_mul]
  by_cases hk : 7≤k
  · rw [operator_large ℚ e d c x k hk,
      operator_large ℚ e d c x (k+1) (by omega),lie_zero,smul_zero]
  · have hlt : k<7 := by omega
    interval_cases k
    · change ⁅e,operator ℚ e d c 0 x⁆=(1:ℚ) • operator ℚ e d c 1 x
      simp only [operator_zero,operator_one,one_smul,Ring.lie_def]
    · change ⁅e,operator ℚ e d c 1 x⁆=(2:ℚ) • operator ℚ e d c 2 x
      rw [show (2:ℚ)=1+1 by norm_num]
      simp only [operator_one,operator_two,add_smul,one_smul,Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]
    · change ⁅e,operator ℚ e d c 2 x⁆=(3:ℚ) • operator ℚ e d c 3 x
      rw [show (3:ℚ)=1+1+1 by norm_num]
      simp only [operator_two,operator_three,add_smul,one_smul,Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]
    · change ⁅e,operator ℚ e d c 3 x⁆=(4:ℚ) • operator ℚ e d c 4 x
      rw [show (4:ℚ)=1+1+1+1 by norm_num]
      simp only [operator_three,operator_four,add_smul,one_smul,Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]
    · change ⁅e,operator ℚ e d c 4 x⁆=(5:ℚ) • operator ℚ e d c 5 x
      rw [show (5:ℚ)=1+1+1+1+1 by norm_num]
      simp only [operator_four,operator_five,add_smul,one_smul,Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]
    · change ⁅e,operator ℚ e d c 5 x⁆=(6:ℚ) • operator ℚ e d c 6 x
      rw [show (6:ℚ)=1+1+1+1+1+1 by norm_num]
      simp only [operator_five,operator_six,add_smul,one_smul,Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]
    · rw [operator_six,operator_large ℚ e d c x 7 (by decide),smul_zero]
      simp only [Ring.lie_def]
      noncomm_ring [hee,hed,hde,hec,hce,eeL,edL,deL,ecL,ceL]

theorem ad_pow_eq_factorial_operator (k : ℕ) (x : B) :
    (LieAlgebra.ad ℚ B e^k) x=(k.factorial:ℚ) • operator ℚ e d c k x := by
  induction k with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.factorial_zero,
      Nat.cast_one,one_smul,operator_zero]
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    change ⁅e,(k.factorial:ℚ) • operator ℚ e d c k x⁆=_
    rw [lie_smul,ad_operator e d c hee hed hde hec hce,smul_smul]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    congr 1
    exact mul_comm _ _

theorem rational_operator (k : ℕ) (x : B) :
    CFSGSquareZeroDividedPowers.operator e k x=operator ℚ e d c k x := by
  unfold CFSGSquareZeroDividedPowers.operator
  rw [LinearMap.smul_apply,ad_pow_eq_factorial_operator e d c hee hed hde hec hce,smul_smul]
  have hk : (k.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [inv_mul_cancel₀ hk,one_smul]

end SymmetricSubgroupAsymptotics.CFSGCubicRootDividedPowers
