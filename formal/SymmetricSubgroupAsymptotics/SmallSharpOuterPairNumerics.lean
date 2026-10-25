import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.UnitLogOrdinaryGeneratorTail
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! Uniform arithmetic for sharp outer-order bounds on generating pairs.
The small ranges are integer inequalities, not an action catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
open IntegerLogSquareRootCeilingCertificate

theorem cardFactors_le_of_lt_pow (N k : ℕ) (hN : 0<N) (hb : N<2^(k+1)) :
    ArithmeticFunction.cardFactors N ≤ k := by
  have hlog := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
    (by exact_mod_cast hN : (0:ℝ)<N)
    (by exact_mod_cast hb : (N:ℝ)<(2:ℝ)^(k+1))
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hlog
  have hc := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb N hN.ne').trans_lt hlog
  have hcN : ArithmeticFunction.cardFactors N<k+1 := by exact_mod_cast hc
  omega

theorem five_le_ceiling (n : ℕ) (hn : 7≤n) :
    5≤traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 32≤n
  · have hlog : 0≤Real.logb 2 (n:ℝ) :=
      (Real.logb_pos (by norm_num : (1:ℝ)<2)
        (by exact_mod_cast (show 1<n by omega))).le
    have hh := (UnitLogOrdinaryGeneratorTail.aggregate_le n hlarge).trans
      (Nat.le_ceil ((n:ℝ)/Real.sqrt (Real.logb 2 (n:ℝ))))
    change Real.logb 2 (n:ℝ)+5≤(traceyPermutationGeneratorCeiling n:ℝ) at hh
    have hc : (5:ℝ)≤(traceyPermutationGeneratorCeiling n:ℝ) := by linarith
    exact_mod_cast hc
  · by_cases hsmall : n≤8
    · change 5≤⌈(n:ℝ)/Real.sqrt (Real.logb 2 (n:ℝ))⌉₊
      apply le_ceil_of_square n 1 3 5 (by omega) (by decide) (by decide)
      · simpa using hsmall
      · have hnR : 7≤n := hn
        nlinarith
    · change 5≤⌈(n:ℝ)/Real.sqrt (Real.logb 2 (n:ℝ))⌉₊
      apply le_ceil_of_square n 1 5 5 (by omega) (by decide) (by decide)
      · simpa using (show n≤32 by omega)
      · have hnR : 9≤n := by omega
        nlinarith

theorem four_le_ceiling (n : ℕ) (hn : 5≤n) :
    4≤traceyPermutationGeneratorCeiling n := by
  by_cases hseven : 7≤n
  · exact (by decide : 4≤5).trans (five_le_ceiling n hseven)
  · have hcases : n=5 ∨ n=6 := by omega
    rcases hcases with rfl|rfl
    · exact le_ceil_of_square 5 3 7 4 (by decide) (by decide) (by decide)
        (by decide) (by decide)
    · exact le_ceil_of_square 6 1 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide)

theorem sharp_outer_small_multiplicity (n N : ℕ) (hn : 5≤n) (hsmall : n<32)
    (hN : 0<N) (hb : (N:ℝ)≤3*Real.logb 2 (n:ℝ)) :
    2+ArithmeticFunction.cardFactors N≤traceyPermutationGeneratorCeiling n := by
  by_cases hseven : 7≤n
  · have hlog := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast (show 0<n by omega) : (0:ℝ)<n)
      (by exact_mod_cast hsmall : (n:ℝ)<32)
    have h32 : Real.logb 2 (32:ℝ)=5 := by
      rw [show (32:ℝ)=2^5 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
      norm_num
    rw [h32] at hlog
    have hb16 : N<2^(3+1) := by
      have : (N:ℝ)<16 := by linarith
      exact_mod_cast this
    have hc := cardFactors_le_of_lt_pow N 3 hN hb16
    exact (Nat.add_le_add_left hc 2).trans (five_le_ceiling n hseven)
  · have hn6 : n≤6 := by omega
    have hn3 : n^3<2^8 := by
      have hpow := Nat.pow_le_pow_left hn6 3
      norm_num at hpow ⊢
      omega
    have hlog := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
      (by positivity : (0:ℝ)<(n:ℝ)^3)
      (by exact_mod_cast hn3 : (n:ℝ)^3<(2:ℝ)^8)
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hlog
    have hb8 : N<2^(2+1) := by
      have : (N:ℝ)<8 := hb.trans_lt hlog
      exact_mod_cast this
    have hc := cardFactors_le_of_lt_pow N 2 hN hb8
    exact (Nat.add_le_add_left hc 2).trans (four_le_ceiling n hn)

end SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
