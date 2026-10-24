import SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics

/-! Actual ordinary costs for product-index socle actions. The simple
rank comes from its genuine smaller transitive coset action, and the
quotient is the original full-socle quotient. The outer-order hypothesis
is a group bound, not a numerical fitting condition. No simple
two-generation theorem or global permutation-generator theorem is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryCost
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

theorem ceiling_le_degree (ell : ℕ) (hell : 2 ≤ ell) :
    traceyPermutationGeneratorCeiling ell ≤ ell := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hL : 1 ≤ Real.logb 2 (ell : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) he
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hs : 1 ≤ Real.sqrt (Real.logb 2 (ell : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  change ⌈(ell : ℝ)/Real.sqrt (Real.logb 2 (ell : ℝ))⌉₊ ≤ ell
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (Real.logb 2 (ell : ℝ)))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ ell by positivity)]

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_square_root_log_cost (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex D.Simple ell)
    (hk : 2 ≤ D.factorCount) (hdegree : ell^D.factorCount ≤ n)
    (hout : (Nat.card (Outer D.Simple) : ℝ) ≤
      6*Real.logb 2 (Nat.card D.Simple : ℝ)) :
    (MarkedC4.genRank G : ℝ) ≤ 2*Real.sqrt (n : ℝ)+
      (Real.logb 2 (n : ℝ))^2+5*Real.logb 2 (n : ℝ) := by
  obtain ⟨H,hH,hindex⟩ := hell.1
  have hell2 : 2 ≤ ell := by
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hell0 : 0 < ell := by omega
  have hpow : ell^2 ≤ n :=
    (Nat.pow_le_pow_right hell0 hk).trans hdegree
  have hlt : ell < n := by
    have hh : ell < ell^2 := by nlinarith only [hell2]
    exact hh.trans_le hpow
  have hrec := PrimitiveSocleStrictOuterOrdinaryRecurrence.genRank_le_strict_simple_add_outer_multiplicity
    D n ell hbelow hell hlt
  have hrecR : (MarkedC4.genRank G : ℝ) ≤
      2*(traceyPermutationGeneratorCeiling ell : ℝ)+
        (D.factorCount : ℝ)*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
          ArithmeticFunction.cardFactors D.factorCount.factorial := by
    exact_mod_cast hrec
  have hceil : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ ell := by
    exact_mod_cast ceiling_le_degree ell hell2
  have hellSq : (ell : ℝ)^2 ≤ n := by exact_mod_cast hpow
  have hellSqrt : (ell : ℝ) ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hellSq
  let l := Real.logb 2 (ell : ℝ)
  let L := Real.logb 2 (n : ℝ)
  have hl : 1 ≤ l := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ ell by exact_mod_cast hell2)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hk0 : (0 : ℝ) ≤ D.factorCount := by positivity
  have hkl : (D.factorCount : ℝ)*l ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by exact_mod_cast hell0 : (0 : ℝ) < ell) D.factorCount)
      (show (ell : ℝ)^D.factorCount ≤ n by exact_mod_cast hdegree)
    simpa only [Real.logb_pow] using hh
  have hkL : (D.factorCount : ℝ) ≤ L := by
    nlinarith only [hkl,mul_le_mul_of_nonneg_left hl hk0]
  have hL0 : 0 ≤ L := hk0.trans hkL
  have hkSq : (D.factorCount : ℝ)^2 ≤ L^2 := (sq_le_sq₀ hk0 hL0).mpr hkL
  have hsimpleOrder : (Nat.card D.Simple : ℝ) ≤ ell.factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos ell)
      (SimpleLeastIndexStrictOrdinaryGenerators.card_dvd_factorial D.Simple ell hell)
  have hsimpleLog : Real.logb 2 (Nat.card D.Simple : ℝ) ≤ (ell : ℝ)^2 := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := D.Simple))) hsimpleOrder
    exact hh.trans (CFSGCoarsePrimitiveNumerics.factorial_logb_le_square ell)
  have houtPoly : (Nat.card (Outer D.Simple) : ℝ) ≤ 8*(ell : ℝ)^2 := by
    nlinarith only [hout,hsimpleLog,sq_nonneg (ell : ℝ)]
  have houtLog : Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤ 3+2*l := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple))) houtPoly
    rw [Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0)
      (pow_ne_zero _ (by exact_mod_cast hell0.ne' : (ell : ℝ) ≠ 0)),
      Real.logb_pow] at hh
    have h8 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    simpa only [h8,Nat.cast_ofNat] using hh
  have houtOmega := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans houtLog
  have houter := mul_le_mul_of_nonneg_left houtOmega hk0
  have houterCost : (D.factorCount : ℝ)*
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 5*L := by
    nlinarith only [houter,hkl,hkL]
  have hfact := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    D.factorCount.factorial (Nat.factorial_pos D.factorCount).ne').trans
      ((CFSGCoarsePrimitiveNumerics.factorial_logb_le_square D.factorCount).trans hkSq)
  change (MarkedC4.genRank G : ℝ) ≤ 2*Real.sqrt (n : ℝ)+L^2+5*L
  linarith only [hrecR,hceil,hellSqrt,houterCost,hfact]

end SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryCost
