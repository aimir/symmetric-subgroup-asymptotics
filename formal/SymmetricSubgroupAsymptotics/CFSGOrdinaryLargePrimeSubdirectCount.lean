import SymmetricSubgroupAsymptotics.CFSGOrdinarySubdirectCount
import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActualDegreeProfile

/-! The ordinary subdirect quadratic bound for every prime at least five.
Only actual transitive prime-permutation factors occur, and all uniform
normal-rank and order premises of the numerical incidence bound are proved
internally from their original actions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryLargePrimeSubdirectCount
open MarkedC4 CFSGPrimeOrdinaryFactorProfile

theorem prime_coefficient_le {p : ℕ} (hp : 5 ≤ p) :
    (Real.logb 2 p/(p-1))*(1/(p : ℝ))/4 ≤ 1/16 := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpred : (0 : ℝ) < p-1 := by
    have h : (5 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hlog : Real.logb 2 p ≤ (p : ℝ) := by
    have hn : p ≤ 2^p := (Nat.lt_two_pow_self (n := p)).le
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpR
      (show (p : ℝ) ≤ (2 : ℝ)^p by exact_mod_cast hn)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] using hh
  have hfirst : (Real.logb 2 p/(p-1))*(1/(p : ℝ)) ≤ 1/(p-1) := by
    apply (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hlog hpred.le) (one_div_nonneg.mpr hpR.le)).trans_eq
    field_simp [ne_of_gt hpR,ne_of_gt hpred]
  have hlast : 1/(p-1) ≤ (1/4 : ℝ) := by
    apply (div_le_iff₀ hpred).mpr
    have h : (5 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  linarith

/-- All nilpotent subdirect sources, all selected orders, and all tableau
menus are counted. No odd-prime classification or subgroup-count input is
retained. B and K only bound the finitely many actual physical factors. -/
theorem subdirect_card_le (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {t : ℕ} (X : Fin t → Type) [∀ i,Finite (X i)] [∀ i,Nonempty (X i)]
    (U : ∀ i,Subgroup (Equiv.Perm (X i)))
    [∀ i,MulAction.IsPretransitive (U i) (X i)]
    (hU : ∀ i,IsPGroup p (U i)) (B : ℝ) (K : ℕ)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (U i)) ≤ B)
    (hK : ∀ i,Nat.card (U i) ≤ K) :
    (Nat.card (ActualWordMenuPartition.Family (fun i => U i)) : ℝ) ≤
      (t.factorial*(t+1)^((2^K)*t) : ℕ)*
        (2 : ℝ)^((∑ i : Fin t,(Nat.card (X i) : ℝ))^2/16+(t : ℝ)*B^2) := by
  let C : ℝ := Real.logb 2 p/(p-1)
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hC : 0 < C := div_pos
    (Real.logb_pos (by norm_num) hpR) (by linarith)
  have hc := CFSGOrdinarySubdirectCount.subdirect_card_le (fun i => U i)
    (fun i => Nat.card (X i)) C (1/(p : ℝ)) B K hC (by positivity)
    (fun i => Nat.card_pos)
    (by
      intro i
      exact log_order_le p (U i) (hU i))
    hbounded hK
    (by
      intro i N _
      have h := CFSGPrimeOrdinaryActualDegreeProfile.normalGen_real_le_div p (U i) (hU i) N
      simpa only [one_div_mul_eq_div] using h)
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hm := mul_le_mul_of_nonneg_right (prime_coefficient_le hp)
    (sq_nonneg (∑ i : Fin t,(Nat.card (X i) : ℝ)))
  dsimp [C]
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGOrdinaryLargePrimeSubdirectCount
