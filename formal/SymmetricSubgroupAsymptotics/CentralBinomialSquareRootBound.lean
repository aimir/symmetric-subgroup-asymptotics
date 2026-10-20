import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! An elementary squared Wallis estimate with the constant required by
all primary induced-module consumers. No asymptotic binomial theorem is
assumed; the central recurrence gives a finite algebraic induction. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CentralBinomialSquareRootBound

theorem even_square (m : ℕ) :
    (3*(m : ℝ)+1)*(m.centralBinom : ℝ)^2 ≤ (16 : ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hr : ((m : ℝ)+1)*((m+1).centralBinom : ℝ)=
        2*(2*(m : ℝ)+1)*(m.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hpoly : (3*((m : ℝ)+1)+1)*(2*(2*(m : ℝ)+1))^2 ≤
        16*((m : ℝ)+1)^2*(3*(m : ℝ)+1) := by nlinarith
    have hpos : 0 < ((m : ℝ)+1)^2 := by positivity
    apply (mul_le_mul_iff_left₀ hpos).mp
    push_cast
    calc
      (3*((m : ℝ)+1)+1)*((m+1).centralBinom : ℝ)^2*((m : ℝ)+1)^2 =
          (3*((m : ℝ)+1)+1)*(((m : ℝ)+1)*((m+1).centralBinom : ℝ))^2 := by ring
      _ = (3*((m : ℝ)+1)+1)*(2*(2*(m : ℝ)+1))^2*(m.centralBinom : ℝ)^2 := by rw [hr];ring
      _ ≤ (16*((m : ℝ)+1)^2*(3*(m : ℝ)+1))*(m.centralBinom : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)
      _ = 16*((m : ℝ)+1)^2*((3*(m : ℝ)+1)*(m.centralBinom : ℝ)^2) := by ring
      _ ≤ 16*((m : ℝ)+1)^2*(16 : ℝ)^m := by gcongr
      _ = (16 : ℝ)^(m+1)*((m : ℝ)+1)^2 := by rw [pow_succ];ring

theorem odd_central (m : ℕ) :
    (m+1).centralBinom = 2*(2*m+1).choose m := by
  rw [Nat.centralBinom_eq_two_mul_choose,show 2*(m+1)=(2*m+1)+1 by omega,
    Nat.choose_succ_succ]
  have hs : (2*m+1).choose (m+1)=(2*m+1).choose m := by
    simpa only [show 2*m+1-(m+1)=m by omega] using
      (Nat.choose_symm (by omega : m+1≤2*m+1)).symm
  rw [hs]
  omega

theorem normalized_square (n : ℕ) :
    (3*(n : ℝ)+2)*((n.choose (n/2) : ℝ)/(2 : ℝ)^n)^2 ≤ 2 := by
  obtain ⟨m,he | he⟩ := Nat.even_or_odd' n
  · subst n
    have h := even_square m
    rw [Nat.mul_div_cancel_left m (by decide : 0<2)]
    rw [← Nat.centralBinom_eq_two_mul_choose]
    have hp : ((2 : ℝ)^(2*m))^2=(16 : ℝ)^m := by
      rw [← pow_mul,show (2*m)*2=4*m by omega,pow_mul];norm_num
    rw [div_pow,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<((2 : ℝ)^(2*m))^2)).mpr
    rw [hp]
    push_cast
    nlinarith [h]
  · subst n
    have h := even_square (m+1)
    have hc : ((m+1).centralBinom : ℝ)=2*((2*m+1).choose m : ℝ) := by
      exact_mod_cast odd_central m
    have hp : ((2 : ℝ)^(2*m+1))^2=(16 : ℝ)^m*4 := by
      calc
        ((2 : ℝ)^(2*m+1))^2 = ((2 : ℝ)^(2*m))^2*4 := by
          rw [show (2 : ℝ)^(2*m+1)=(2 : ℝ)^(2*m)*2 by rw [pow_succ]]
          ring
        _ = (16 : ℝ)^m*4 := by
          rw [← pow_mul,show (2*m)*2=4*m by omega,pow_mul]
          norm_num
    have hm : (2*m+1)/2=m := by omega
    rw [hm,div_pow,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<((2 : ℝ)^(2*m+1))^2)).mpr
    rw [hp]
    push_cast at h ⊢
    rw [show (16 : ℝ)^(m+1)=(16 : ℝ)^m*16 by rw [pow_succ],hc] at h
    nlinarith [sq_nonneg (((2*m+1).choose m : ℝ))]

theorem normalized_le_sqrt (n : ℕ) (hn : 1≤n) :
    (n.choose (n/2) : ℝ)/(2 : ℝ)^n ≤ Real.sqrt (2/(3*(n : ℝ))) := by
  have h := normalized_square n
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn
  have hd : (0 : ℝ)<3*(n : ℝ) := by positivity
  have hs : ((n.choose (n/2) : ℝ)/(2 : ℝ)^n)^2 ≤ 2/(3*(n : ℝ)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg ((n.choose (n/2) : ℝ)/(2 : ℝ)^n)]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hs

end SymmetricSubgroupAsymptotics.CentralBinomialSquareRootBound
