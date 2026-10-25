import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! Actual multi-factor socles in local degree32..127 have two uniform
parameter bands. The constraints follow from the SAME degree form and
outer packet, not a finite classification or supplied rank certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeMultipleHeadParameters
open PrimitiveSocleRawStructure

theorem parameters {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hr : 32 ≤ Nat.card X) (hsmall : Nat.card X < 128)
    (hk2 : 2 ≤ D.factorCount) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (Nat.card X < 64 ∧ traceyPermutationGeneratorCeiling ell ≤ 5 ∧
      D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial ≤ 7) ∨
    (64 ≤ Nat.card X ∧ traceyPermutationGeneratorCeiling ell ≤ 6 ∧
      D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial ≤ 11) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hfive := (Nat.pow_le_pow_left hell5 D.factorCount).trans hdegree
  have hk3 : D.factorCount ≤ 3 := by
    by_contra hh
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 5) (show 4 ≤ D.factorCount by omega)).trans hfive
    norm_num at hp
    omega
  have hsquare : ell^2 ≤ Nat.card X :=
    (Nat.pow_le_pow_right (show 0 < ell by omega) hk2).trans hdegree
  have hell11 : ell ≤ 11 := by
    by_contra hh
    have hp := Nat.pow_le_pow_left (show 12 ≤ ell by omega) 2
    norm_num at hp
    omega
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega) : (0 : ℝ) < ell)
    (show (ell : ℝ) < 16 by exact_mod_cast (show ell < 16 by omega))
  have h16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2^4 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [h16] at hlog
  have hout := houter.log_three_of_small (by omega)
  have hN : Nat.card (Outer D.Simple) < 2^(3+1) := by
    have hh : (Nat.card (Outer D.Simple) : ℝ) < 16 := by linarith only [hout,hlog]
    exact_mod_cast hh
  have hOmega := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 3 Nat.card_pos hN
  have hfac2 : ArithmeticFunction.cardFactors (2 : ℕ).factorial = 1 := by decide +kernel
  have hfac3 : ArithmeticFunction.cardFactors (3 : ℕ).factorial = 2 := by decide +kernel
  by_cases h64 : Nat.card X < 64
  · have hk : D.factorCount = 2 := by
      by_contra hh
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
        (show 3 ≤ D.factorCount by omega)).trans hfive
      norm_num at hp
      omega
    have hell7 : ell ≤ 7 := by
      by_contra hh
      have hp := Nat.pow_le_pow_left (show 8 ≤ ell by omega) 2
      norm_num at hp
      omega
    have hceil7 : traceyPermutationGeneratorCeiling 7 ≤ 5 :=
      IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 7 1 2 5
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hc := (TraceyCoarseCeilingMonotonicity.ceiling_mono (by omega : 2 ≤ ell) hell7).trans hceil7
    left
    refine ⟨h64,hc,?_⟩
    rw [hk,hfac2]
    omega
  · have hceil11 : traceyPermutationGeneratorCeiling 11 ≤ 6 :=
      IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 11 8 27 6
        (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
    have hc := (TraceyCoarseCeilingMonotonicity.ceiling_mono (by omega : 2 ≤ ell) hell11).trans hceil11
    right
    refine ⟨by omega,hc,?_⟩
    have hk : D.factorCount = 2 ∨ D.factorCount = 3 := by omega
    rcases hk with hk | hk
    · rw [hk,hfac2]; omega
    · rw [hk,hfac3]; omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeMultipleHeadParameters
