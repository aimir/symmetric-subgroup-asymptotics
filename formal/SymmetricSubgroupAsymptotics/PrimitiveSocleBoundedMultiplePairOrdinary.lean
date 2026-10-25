import SymmetricSubgroupAsymptotics.PrimitiveSocleMultipleFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! One bounded parameter argument for every primitive multifactor socle
whose actual simple group has generator rank at most two. No action
catalogue or pointwise numerical fitting is used. The quotient remains
the full original socle quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedMultiplePairOrdinary
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem bounded_genRank_le_ceiling (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hk2 : 2 ≤ D.factorCount)
    (horder : ell^2 < Nat.card D.Simple) (hsmall : Nat.card X < 1024)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hsimple : MarkedC4.genRank D.Simple ≤ 2) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hfive := (Nat.pow_le_pow_left hell5 D.factorCount).trans hdegree
  have h25 : 25 ≤ Nat.card X := by
    have hh := (Nat.pow_le_pow_right (by decide : 0 < 5) hk2).trans hfive
    norm_num at hh
    exact hh
  have hk4 : D.factorCount ≤ 4 := by
    by_contra hh
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 5 ≤ D.factorCount by omega)).trans hfive
    norm_num at hp
    omega
  have hsquare : ell^2 ≤ Nat.card X :=
    (Nat.pow_le_pow_right (show 0 < ell by omega) hk2).trans hdegree
  have hell32 : ell < 32 := by
    by_contra hh
    have hp := Nat.pow_le_pow_left (show 32 ≤ ell by omega) 2
    norm_num at hp
    omega
  have hcost : MarkedC4.genRank G ≤ 4+
      D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial := by
    have hc := PrimitiveSocleIsotypicOrdinaryCompression.genRank_le_twice_simple_add_quotient D
    have hq := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_genRank_le_outer_multiplicity D
    omega
  by_cases h64 : Nat.card X < 64
  · have hk : D.factorCount=2 := by
      by_contra hh
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
        (show 3 ≤ D.factorCount by omega)).trans hfive
      norm_num at hp
      omega
    have hell8 : ell < 8 := by
      by_contra hh
      have hp := Nat.pow_le_pow_left (show 8 ≤ ell by omega) 2
      norm_num at hp
      omega
    have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 0 < ell by omega) : (0 : ℝ) < ell)
      (show (ell : ℝ) < (2 : ℝ)^3 by exact_mod_cast hell8)
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] at hl
    norm_num at hl
    have ho := houter.log_three_of_small (by omega)
    have hout : Nat.card (Outer D.Simple)<2^(3+1) := by
      have hh : (Nat.card (Outer D.Simple) : ℝ)<16 := by linarith only [ho,hl]
      exact_mod_cast hh
    have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
      (Nat.card (Outer D.Simple)) 3 Nat.card_pos hout
    have hf : ArithmeticFunction.cardFactors (2 : ℕ).factorial=1 := by decide +kernel
    rw [hk,hf] at hcost
    have h11 : MarkedC4.genRank G ≤ 11 := by omega
    have hbase : 12 ≤ traceyPermutationGeneratorCeiling 25 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 25 1 5 12
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h11.trans ((by omega : 11 ≤ 12).trans (hbase.trans
      (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide : 2 ≤ 25) h25)))
  · have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 0 < ell by omega) : (0 : ℝ) < ell)
      (show (ell : ℝ) < (2 : ℝ)^5 by exact_mod_cast hell32)
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] at hl
    norm_num at hl
    have ho := houter.log_six
    have hout : Nat.card (Outer D.Simple)<2^(4+1) := by
      have hh : (Nat.card (Outer D.Simple) : ℝ)<32 := by linarith only [ho,hl]
      exact_mod_cast hh
    have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
      (Nat.card (Outer D.Simple)) 4 Nat.card_pos hout
    have hfact := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
      (Nat.factorial_pos D.factorCount).ne' (Nat.factorial_pos 4).ne'
      (Nat.factorial_dvd_factorial hk4)
    have hf : ArithmeticFunction.cardFactors (4 : ℕ).factorial=4 := by decide +kernel
    rw [hf] at hfact
    have hmul := Nat.mul_le_mul hk4 hmu
    have h24 : MarkedC4.genRank G ≤ 24 := by omega
    have hbase : 24 ≤ traceyPermutationGeneratorCeiling 64 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 64 1 6 24
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h24.trans (hbase.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono
      (by decide : 2 ≤ 64) (by omega)))

theorem genRank_le_ceiling (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk2 : 2 ≤ D.factorCount)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hsimple : MarkedC4.genRank D.Simple ≤ 2) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hn : 1024 ≤ Nat.card X
  · exact PrimitiveSocleMultipleFactorOrdinaryTail.genRank_le_ceiling
      D ell hbelow hell hk2 horder hn houter
  · exact bounded_genRank_le_ceiling D ell hell hk2 horder (by omega) houter hsimple

end SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedMultiplePairOrdinary
