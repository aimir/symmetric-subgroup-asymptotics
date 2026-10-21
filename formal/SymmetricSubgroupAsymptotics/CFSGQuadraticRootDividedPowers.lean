import SymmetricSubgroupAsymptotics.CFSGIntegralQuadraticRootOperators
import SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
import Mathlib.Tactic.NoncommRing

/-! Actual factorial identities for a quadratic integral root exponential.
They retain the fourth adjoint coefficient and prove all higher ones zero;
there is no uniform four-term truncation premise. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootDividedPowers
open CFSGIntegralQuadraticRootOperators
variable {B : Type*} [Ring B] [Algebra ℚ B]
    (e d : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0)
private theorem two_smul_eq (y : B) : (2:ℚ) • y=y+y := by
  rw [show (2:ℚ)=1+1 by norm_num,add_smul,one_smul]
private theorem three_smul_eq (y : B) : (3:ℚ) • y=y+y+y := by
  rw [show (3:ℚ)=1+1+1 by norm_num,add_smul,add_smul,one_smul]
private theorem four_smul_eq (y : B) : (4:ℚ) • y=y+y+y+y := by
  rw [show (4:ℚ)=1+1+1+1 by norm_num,add_smul,add_smul,add_smul,one_smul]

include he hed hde

theorem ad_operator (k : ℕ) (x : B) :
    ⁅e,operator ℚ e d k x⁆=((k+1:ℕ):ℚ) • operator ℚ e d (k+1) x := by
  by_cases hk : 5≤k
  · rw [operator_large ℚ e d x k hk,
      operator_large ℚ e d x (k+1) (by omega),lie_zero,smul_zero]
  · have hlt : k<5 := by omega
    interval_cases k
    · change ⁅e,operator ℚ e d 0 x⁆=(1:ℚ) • operator ℚ e d 1 x
      simp only [operator_zero,operator_one,one_smul,Ring.lie_def]
    · change ⁅e,operator ℚ e d 1 x⁆=(2:ℚ) • operator ℚ e d 2 x
      simp only [operator_one,operator_two]
      norm_num only [Nat.cast_ofNat]
      rw [two_smul_eq]
      have hh : ⁅e,e*x-x*e⁆=(e*e)*x+x*(e*e)-(e*x*e+e*x*e) := by
        simp only [Ring.lie_def]
        noncomm_ring
      rw [hh,he]
      noncomm_ring
    · change ⁅e,operator ℚ e d 2 x⁆=(3:ℚ) • operator ℚ e d 3 x
      simp only [operator_two,operator_three]
      norm_num only [Nat.cast_ofNat]
      rw [three_smul_eq]
      have hh : ⁅e,d*x+x*d-e*x*e⁆=
          (e*d)*x-d*x*e+e*x*d-x*(d*e)-(e*e)*x*e+e*x*(e*e) := by
        simp only [Ring.lie_def]
        noncomm_ring
      rw [hh,hed,hde,he]
      simp only [zero_mul,mul_zero]
      noncomm_ring
    · change ⁅e,operator ℚ e d 3 x⁆=(4:ℚ) • operator ℚ e d 4 x
      simp only [operator_three,operator_four]
      norm_num only [Nat.cast_ofNat]
      rw [four_smul_eq]
      have hh : ⁅e,e*x*d-d*x*e⁆=
          (e*e)*x*d-(e*d)*x*e-e*x*(d*e)+d*x*(e*e) := by
        simp only [Ring.lie_def]
        noncomm_ring
      rw [hh,hed,hde,he]
      simp only [zero_mul,mul_zero]
      noncomm_ring
    · change ⁅e,operator ℚ e d 4 x⁆=(5:ℚ) • operator ℚ e d 5 x
      rw [operator_four,operator_large ℚ e d x 5 (by decide),smul_zero]
      have hh : ⁅e,d*x*d⁆=(e*d)*x*d-d*x*(d*e) := by
        simp only [Ring.lie_def]
        noncomm_ring
      rw [hh,hed,hde,zero_mul,zero_mul,mul_zero,sub_zero]

theorem ad_pow_eq_factorial_operator (k : ℕ) (x : B) :
    (LieAlgebra.ad ℚ B e ^ k) x=(k.factorial:ℚ) • operator ℚ e d k x := by
  induction k with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.factorial_zero,
      Nat.cast_one,one_smul,operator_zero]
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    change ⁅e,(k.factorial:ℚ) • operator ℚ e d k x⁆=_
    rw [lie_smul,ad_operator e d he hed hde,smul_smul]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    congr 1
    exact mul_comm _ _

theorem rational_operator (k : ℕ) (x : B) :
    CFSGSquareZeroDividedPowers.operator e k x=operator ℚ e d k x := by
  unfold CFSGSquareZeroDividedPowers.operator
  rw [LinearMap.smul_apply]
  rw [ad_pow_eq_factorial_operator e d he hed hde,smul_smul]
  have hk : (k.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [inv_mul_cancel₀ hk,one_smul]

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootDividedPowers
