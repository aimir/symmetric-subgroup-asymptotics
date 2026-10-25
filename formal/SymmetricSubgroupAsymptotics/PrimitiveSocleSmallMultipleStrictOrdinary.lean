import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedMultiplePairOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeMultipleHeadParameters

/-! Uniform bounded multifactor primitive induction without a generating
pair premise. The simple head is paid by its strictly smaller transitive
coset action. Only scalar degree bands are split, never action rows. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSmallMultipleStrictOrdinary
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

private theorem log_power_bound (ell d u : ℕ) (hell : 0 < ell)
    (h : ell^d < 2^u) : (d : ℝ)*Real.logb 2 (ell : ℝ) < u := by
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast hell : (0 : ℝ)<ell) d)
    (show (ell : ℝ)^d < (2 : ℝ)^u by exact_mod_cast h)
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),
    mul_one] using hl

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem bounded_genRank_le_ceiling (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk2 : 2 ≤ D.factorCount)
    (horder : ell^2 < Nat.card D.Simple) (hn : 32 ≤ Nat.card X)
    (hsmall : Nat.card X < 1024)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hell0 : 0 < ell := by omega
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hfive := (Nat.pow_le_pow_left hell5 D.factorCount).trans hdegree
  have hk4 : D.factorCount ≤ 4 := by
    by_contra hh
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 5 ≤ D.factorCount by omega)).trans hfive
    norm_num at hp
    omega
  have hsquare : ell^2 ≤ Nat.card X :=
    (Nat.pow_le_pow_right hell0 hk2).trans hdegree
  have hlt : ell < Nat.card X := by nlinarith only [hsquare,hell5]
  have hell32 : ell < 32 := by
    by_contra hh
    have hp := Nat.pow_le_pow_left (show 32 ≤ ell by omega) 2
    norm_num at hp
    omega
  have hcost := PrimitiveSocleStrictOuterOrdinaryRecurrence.genRank_le_strict_simple_add_outer_multiplicity
    D (Nat.card X) ell hbelow hell hlt
  have hf2 : ArithmeticFunction.cardFactors (2 : ℕ).factorial=1 := by decide +kernel
  by_cases h64 : Nat.card X < 64
  · have hk : D.factorCount=2 := by
      by_contra hh
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
        (show 3 ≤ D.factorCount by omega)).trans hfive
      norm_num at hp
      omega
    rw [hk,hf2] at hcost
    have hell7 : ell ≤ 7 := by
      by_contra hh
      have hp := Nat.pow_le_pow_left (show 8 ≤ ell by omega) 2
      norm_num at hp
      omega
    by_cases h6 : ell ≤ 6
    · have hp : ell^3 < 2^8 :=
        (Nat.pow_le_pow_left h6 3).trans_lt (by decide)
      have hl := log_power_bound ell 3 8 hell0 hp
      norm_num at hl
      have ho := houter.log_three_of_small (by omega)
      have hN : Nat.card (Outer D.Simple)<2^(2+1) := by
        exact_mod_cast (show (Nat.card (Outer D.Simple) : ℝ)<8 by linarith only [ho,hl])
      have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
        (Nat.card (Outer D.Simple)) 2 Nat.card_pos hN
      have hc6 : traceyPermutationGeneratorCeiling 6 ≤ 4 :=
        IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 6 2 5 4
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have hc := (TraceyCoarseCeilingMonotonicity.ceiling_mono (by omega : 2≤ell) h6).trans hc6
      have h13 : MarkedC4.genRank G≤13 := by omega
      have hb : 13 ≤ traceyPermutationGeneratorCeiling 32 :=
        IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 13
          (by decide) (by decide) (by decide) (by decide) (by decide)
      exact h13.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn))
    · have he : ell=7 := by omega
      have hl := log_power_bound ell 1 3 hell0 (by simpa only [he] using (by decide : 7^1<2^3))
      norm_num at hl
      have ho := houter.log_three_of_small (by omega)
      have hN : Nat.card (Outer D.Simple)<2^(3+1) := by
        exact_mod_cast (show (Nat.card (Outer D.Simple) : ℝ)<16 by linarith only [ho,hl])
      have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
        (Nat.card (Outer D.Simple)) 3 Nat.card_pos hN
      have hc : traceyPermutationGeneratorCeiling ell ≤ 5 := by
        rw [he]
        exact IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 7 1 2 5
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have h17 : MarkedC4.genRank G≤17 := by omega
      have h49 : 49≤Nat.card X := by simpa only [he] using hsquare
      have hb : 17 ≤ traceyPermutationGeneratorCeiling 49 :=
        IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 49 1 6 17
          (by decide) (by decide) (by decide) (by decide) (by decide)
      exact h17.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) h49))
  · by_cases h125 : Nat.card X < 125
    · have hk : D.factorCount=2 := by
        by_contra hh
        have hp := (Nat.pow_le_pow_right (by decide : 0 < 5)
          (show 3 ≤ D.factorCount by omega)).trans hfive
        norm_num at hp
        omega
      rw [hk,hf2] at hcost
      have hell11 : ell ≤ 11 := by
        by_contra hh
        have hp := Nat.pow_le_pow_left (show 12 ≤ ell by omega) 2
        norm_num at hp
        omega
      have hl := log_power_bound ell 1 4 hell0 (by simpa using (show ell<16 by omega))
      norm_num at hl
      have ho := houter.log_three_of_small (by omega)
      have hN : Nat.card (Outer D.Simple)<2^(3+1) := by
        exact_mod_cast (show (Nat.card (Outer D.Simple) : ℝ)<16 by linarith only [ho,hl])
      have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
        (Nat.card (Outer D.Simple)) 3 Nat.card_pos hN
      have hc11 : traceyPermutationGeneratorCeiling 11 ≤ 6 :=
        IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 11 8 27 6
          (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
      have hc := (TraceyCoarseCeilingMonotonicity.ceiling_mono (by omega : 2≤ell) hell11).trans hc11
      have h19 : MarkedC4.genRank G≤19 := by omega
      have hb : 19 ≤ traceyPermutationGeneratorCeiling 64 :=
        IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 64 1 6 19
          (by decide) (by decide) (by decide) (by decide) (by decide)
      exact h19.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) (by omega)))
    · have hl := log_power_bound ell 1 5 hell0 (by simpa using hell32)
      norm_num at hl
      have ho := houter.log_six
      have hN : Nat.card (Outer D.Simple)<2^(4+1) := by
        exact_mod_cast (show (Nat.card (Outer D.Simple) : ℝ)<32 by linarith only [ho,hl])
      have hmu := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
        (Nat.card (Outer D.Simple)) 4 Nat.card_pos hN
      have hfact := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
        (Nat.factorial_pos D.factorCount).ne' (Nat.factorial_pos 4).ne'
        (Nat.factorial_dvd_factorial hk4)
      have hf : ArithmeticFunction.cardFactors (4 : ℕ).factorial=4 := by decide +kernel
      rw [hf] at hfact
      have hmul := Nat.mul_le_mul hk4 hmu
      have hc31 : traceyPermutationGeneratorCeiling 31 ≤ 14 :=
        IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 31 11 54 14
          (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
      have hc := (TraceyCoarseCeilingMonotonicity.ceiling_mono (by omega : 2≤ell)
        (show ell≤31 by omega)).trans hc31
      have h48 : MarkedC4.genRank G≤48 := by omega
      have hb : 48 ≤ traceyPermutationGeneratorCeiling 125 :=
        IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 125 1 7 48
          (by decide) (by decide) (by decide) (by decide) (by decide)
      exact h48.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) (by omega)))

theorem genRank_le_ceiling (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk2 : 2 ≤ D.factorCount)
    (horder : ell^2 < Nat.card D.Simple) (hn : 32 ≤ Nat.card X)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleMultipleFactorOrdinaryTail.genRank_le_ceiling
      D ell hbelow hell hk2 horder hlarge houter
  · exact bounded_genRank_le_ceiling D ell hbelow hell hk2 horder hn (by omega) houter

end SymmetricSubgroupAsymptotics.PrimitiveSocleSmallMultipleStrictOrdinary
