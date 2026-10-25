import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! An independent scalar tail for a proved ordinary rank of at most
twice the squared binary logarithm plus the logarithm plus four. No group or permutation input
is asserted by this file. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuadraticLogOrdinaryGeneratorTail

private theorem budget_step (m : ℕ) (hm : 10 ≤ m) :
    (2*(m+1)^2+5*(m+1)+7)^2*(m+1+1) ≤ 4*((2*m^2+5*m+7)^2*(m+1)) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, m = k+10 := ⟨m-10,by omega⟩
  nlinarith only [Nat.zero_le (k^5),Nat.zero_le (k^4),Nat.zero_le (k^3),Nat.zero_le (k^2),Nat.zero_le k]

theorem dyadic_budget (m : ℕ) (hm : 10 ≤ m) : (2*m^2+5*m+7)^2*(m+1) ≤ 4^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      (2*(m+1)^2+5*(m+1)+7)^2*(m+1+1) ≤ 4*((2*m^2+5*m+7)^2*(m+1)) := budget_step m hm
      _ ≤ 4*4^m := Nat.mul_le_mul_left _ ih
      _ = 4^(m+1) := by rw [pow_succ]; omega

theorem aggregate_le (n : ℕ) (hn : 1024 ≤ n) :
    2*(Real.logb 2 (n : ℝ))^2+Real.logb 2 (n : ℝ)+4 ≤ (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
  let m := Nat.log 2 n
  let L := Real.logb 2 (n : ℝ)
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 10 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^10 ≤ n by simpa only [show (2 : ℕ)^10 = 1024 by decide] using hn)
  have hpow : (2 : ℝ)^m ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hn0
  have hL : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have hLu : L ≤ (m : ℝ)+1 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper n 1 (m+1)
      (by omega) (by decide)
      (by simpa only [pow_one] using
        (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le)
    simpa only [L,Nat.cast_add,Nat.cast_one,div_one] using hh
  have hcoef : 2*L^2+L+4 ≤ 2*(m : ℝ)^2+5*(m : ℝ)+7 := by
    have hsquare := (sq_le_sq₀ hL.le (by positivity : 0≤(m : ℝ)+1)).mpr hLu
    nlinarith only [hsquare,hLu]
  have hbudget : (2*(m : ℝ)^2+5*(m : ℝ)+7)^2*((m : ℝ)+1) ≤ (4 : ℝ)^m := by
    exact_mod_cast dyadic_budget m hm
  have hfour : (4 : ℝ)^m = ((2 : ℝ)^m)^2 := by
    calc
      (4 : ℝ)^m = ((2 : ℝ)^2)^m := by norm_num
      _ = (2 : ℝ)^(2*m) := (pow_mul _ _ _).symm
      _ = (2 : ℝ)^(m*2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ)^m)^2 := pow_mul _ _ _
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hsq : ((2*L^2+L+4)*Real.sqrt L)^2 ≤ (n : ℝ)^2 := by
    calc
      _ = (2*L^2+L+4)^2*L := by rw [mul_pow,Real.sq_sqrt hL.le]
      _ ≤ (2*(m : ℝ)^2+5*(m : ℝ)+7)^2*((m : ℝ)+1) :=
        mul_le_mul ((sq_le_sq₀ (by positivity) (by positivity)).mpr hcoef)
          hLu hL.le (sq_nonneg _)
      _ ≤ (4 : ℝ)^m := hbudget
      _ = ((2 : ℝ)^m)^2 := hfour
      _ ≤ (n : ℝ)^2 := (sq_le_sq₀ (by positivity) hnR.le).mpr hpow
  change 2*L^2+L+4 ≤ (n : ℝ)/Real.sqrt L
  exact (le_div_iff₀ hs).mpr ((sq_le_sq₀ (by positivity) hnR.le).mp hsq)

end SymmetricSubgroupAsymptotics.QuadraticLogOrdinaryGeneratorTail
