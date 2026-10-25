import SymmetricSubgroupAsymptotics.PrimitiveSocleOuterMultiplicityDegreeBounds
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! The actual outer-wreath multiplicity in local degrees 25 through 1023.
Only the same simple index/order packet and the actual socle degree form
are used. The four possible factor counts are numerical consequences of
that degree form, not a list of primitive groups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity
open PrimitiveSocleRawStructure

private theorem log_power_lower (c r : ℕ) (hr : 0 < r) (hpow : 2^c ≤ r^2) :
    (c : ℝ) ≤ 2*Real.logb 2 (r : ℝ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^c)
    (show (2 : ℝ)^c ≤ (r : ℝ)^2 by exact_mod_cast hpow)
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] using hh

private theorem outer_small (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell)
    (h32 : ell < 32) : ArithmeticFunction.cardFactors N ≤ 4 := by
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell : (0 : ℝ) < ell)
    (by exact_mod_cast h32 : (ell : ℝ) < 32)
  have hlog : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hlog] at hh
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 4 hN
  have hNR : (N : ℝ) < 32 := by linarith only [houter.log_six,hh]
  exact_mod_cast hNR

private theorem outer_smaller (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell)
    (h16 : ell < 16) : ArithmeticFunction.cardFactors N ≤ 3 := by
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell : (0 : ℝ) < ell)
    (by exact_mod_cast h16 : (ell : ℝ) < 16)
  have hlog : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hlog] at hh
  have hb := houter.log_three_of_small (by omega)
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 3 hN
  have hNR : (N : ℝ) < 16 := by linarith only [hb,hh]
  exact_mod_cast hNR

/-- The same actual outer-wreath coefficient is at most twice the local
logarithm throughout the bounded local-degree band. No generating-pair
or desired ordinary-rank bound is an input. -/
theorem multiplicity_le_twice_log_of_small_degree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hr : 25 ≤ Nat.card X) (hsmall : Nat.card X < 1024)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤
        2*Real.logb 2 (Nat.card X : ℝ) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hfive := (Nat.pow_le_pow_left hell5 D.factorCount).trans hdegree
  have hk : D.factorCount ≤ 4 := by
    by_contra hh
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 5 ≤ D.factorCount by omega)).trans hfive
    norm_num at hpow
    omega
  have hkpos := D.factorCount_pos
  have hcases : D.factorCount = 1 ∨ D.factorCount = 2 ∨
      D.factorCount = 3 ∨ D.factorCount = 4 := by omega
  rcases hcases with hk1 | hk2 | hk3 | hk4
  · have hh := PrimitiveSocleOuterMultiplicityDegreeBounds.multiplicity_le_linear_log_of_one_factor D hk1 ell hell houter
    have hL : 3 ≤ Real.logb 2 (Nat.card X : ℝ) := by
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 8)
        (show (8 : ℝ) ≤ Nat.card X by exact_mod_cast (show 8 ≤ Nat.card X by omega))
      have h8 : Real.logb 2 (8 : ℝ) = 3 := by
        rw [show (8 : ℝ) = 2^3 by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        norm_num
      rwa [h8] at hlog
    linarith only [hh,hL]
  · have h32 : ell < 32 := by
      by_contra hh
      have hpow := Nat.pow_le_pow_left (show 32 ≤ ell by omega) 2
      rw [hk2] at hdegree
      norm_num at hpow
      omega
    have hN := outer_small ell (Nat.card (Outer D.Simple)) Nat.card_pos houter
      (by omega) h32
    have hfac : ArithmeticFunction.cardFactors (2 : ℕ).factorial = 1 := by decide +kernel
    have hc : D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial ≤ 9 := by
      rw [hk2,hfac]
      omega
    have hp : 2^9 ≤ (Nat.card X)^2 := by nlinarith only [hr]
    exact (show ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤ 9 by exact_mod_cast hc).trans
        (log_power_lower 9 (Nat.card X) (by omega) hp)
  · have h16 : ell < 16 := by
      by_contra hh
      have hpow := Nat.pow_le_pow_left (show 16 ≤ ell by omega) 3
      rw [hk3] at hdegree
      norm_num at hpow
      omega
    have hN := outer_smaller ell (Nat.card (Outer D.Simple)) Nat.card_pos houter
      (by omega) h16
    have hfac : ArithmeticFunction.cardFactors (3 : ℕ).factorial = 2 := by decide +kernel
    have hc : D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial ≤ 11 := by
      rw [hk3,hfac]
      omega
    have hr125 : 125 ≤ Nat.card X := by simpa only [hk3] using hfive
    have hp : 2^11 ≤ (Nat.card X)^2 := by nlinarith only [hr125]
    exact (show ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤ 11 by exact_mod_cast hc).trans
        (log_power_lower 11 (Nat.card X) (by omega) hp)
  · have h16 : ell < 16 := by
      by_contra hh
      have hpow := Nat.pow_le_pow_left (show 16 ≤ ell by omega) 4
      rw [hk4] at hdegree
      norm_num at hpow
      omega
    have hN := outer_smaller ell (Nat.card (Outer D.Simple)) Nat.card_pos houter
      (by omega) h16
    have hfac : ArithmeticFunction.cardFactors (4 : ℕ).factorial = 4 := by decide +kernel
    have hc : D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial ≤ 16 := by
      rw [hk4,hfac]
      omega
    have hr625 : 625 ≤ Nat.card X := by simpa only [hk4] using hfive
    have hp : 2^16 ≤ (Nat.card X)^2 := by nlinarith only [hr625]
    exact (show ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤ 16 by exact_mod_cast hc).trans
        (log_power_lower 16 (Nat.card X) (by omega) hp)

end SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity
