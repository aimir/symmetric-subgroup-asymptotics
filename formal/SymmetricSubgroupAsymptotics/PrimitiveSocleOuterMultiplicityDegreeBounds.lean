import SymmetricSubgroupAsymptotics.PrimitiveSocleMultipleFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! Degree control of the ACTUAL outer-wreath prime multiplicity. The
retained local sufficient packet is used at its original least index;
no weakening to the simple-group order and no source-rank fitting premise
is needed. Final family consumers must supply the packet internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOuterMultiplicityDegreeBounds
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

private theorem outer_omega_le_three_add_log (ell : ℕ) (hell2 : 2 ≤ ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤
      3+Real.logb 2 (ell : ℝ) := by
  have hell0 : 0 < ell := by omega
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one ell hell2
  have hout : (Nat.card (Outer D.Simple) : ℝ) ≤ 8*(ell : ℝ) := by
    nlinarith only [houter.log_six,hlog,show (2 : ℝ) ≤ ell by exact_mod_cast hell2]
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast Nat.card_pos (α := Outer D.Simple)) hout
  rw [Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0)
    (by exact_mod_cast hell0.ne' : (ell : ℝ) ≠ 0)] at hh
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [h8] at hh
  exact (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans hh

/-- Actual full-socle geometry and the same simple index/outer packet bound
the quotient multiplicity by a quadratic in the LOCAL degree logarithm. -/
theorem multiplicity_le_quadratic_log (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤
        (Real.logb 2 (Nat.card X : ℝ))^2+4*Real.logb 2 (Nat.card X : ℝ) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hell0 : 0 < ell := by omega
  have hdegree : ell^D.factorCount ≤ Nat.card X :=
    primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  let l := Real.logb 2 (ell : ℝ)
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hl : 1 ≤ l := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ ell by exact_mod_cast (show 2 ≤ ell by omega))
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hk0 : (0 : ℝ) ≤ D.factorCount := by positivity
  have hkl : (D.factorCount : ℝ)*l ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by exact_mod_cast hell0 : (0 : ℝ) < ell) D.factorCount)
      (show (ell : ℝ)^D.factorCount ≤ Nat.card X by exact_mod_cast hdegree)
    simpa only [Real.logb_pow] using hh
  have hkL : (D.factorCount : ℝ) ≤ L := by
    nlinarith only [hkl,mul_le_mul_of_nonneg_left hl hk0]
  have hL0 : 0 ≤ L := hk0.trans hkL
  have hkSq : (D.factorCount : ℝ)^2 ≤ L^2 := (sq_le_sq₀ hk0 hL0).mpr hkL
  have hout := mul_le_mul_of_nonneg_left
    (outer_omega_le_three_add_log D ell (by omega) houter) hk0
  have houtCost : (D.factorCount : ℝ)*
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 4*L := by
    nlinarith only [hout,hkl,hkL]
  have hfact := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    D.factorCount.factorial (Nat.factorial_pos D.factorCount).ne').trans
      ((CFSGCoarsePrimitiveNumerics.factorial_logb_le_square D.factorCount).trans hkSq)
  change ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤ L^2+4*L
  push_cast
  linarith only [houtCost,hfact]

/-- A one-factor local component has only LINEAR outer multiplicity. -/
theorem multiplicity_le_linear_log_of_one_factor (hk : D.factorCount = 1)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) ≤
        3+Real.logb 2 (Nat.card X : ℝ) := by
  have hell2 : 2 ≤ ell := by
    obtain ⟨H,hH,hindex⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hle := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega)) (show (ell : ℝ) ≤ Nat.card X by exact_mod_cast hle)
  have hh := (outer_omega_le_three_add_log D ell hell2 houter).trans
    (add_le_add (le_refl (3 : ℝ)) hlog)
  simpa only [hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,
    Nat.add_zero] using hh

end SymmetricSubgroupAsymptotics.PrimitiveSocleOuterMultiplicityDegreeBounds
