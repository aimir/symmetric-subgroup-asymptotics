import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimePowerProperIndexExponentBound
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex
/-! The whole triality one-factor primitive ordinary branch. Actual
root-Sylow order, outer order and proper index bounds pay every field
through two exponent bands. No action census or pair premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGTrialityGeckOriginalRootFamily

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleTrialityOneFactorOrdinaryTail.genRank_le_ceiling D hk q e hlarge
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H,hH,hindex⟩ := hm.1
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hi : q.prime*q.order^4 ≤ Nat.card X :=
    ((CFSGTrialityGeckMiddlePairingIndex.typeTriality_middle_le_proper_index q H hH).trans_eq hindex).trans hdegree
  have hsize : 2*q.order^4 ≤ Nat.card X :=
    (Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans hi
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hminimum : 32 ≤ Nat.card X :=
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hq2 4)).trans hsize
  let P := originalSylow q
  have hP : Nat.card P ∣ q.prime^(q.exponent*12) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGTrialityGeckOriginalFiniteBruhatCover.originalSylow_card_le q

    change Nat.card P ≤ (q.prime^q.exponent)^12 at hc
    simpa only [pow_mul] using hc
  have hhead : MarkedC4.genRank D.Simple ≤ q.exponent*12+1 :=
    GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      q.prime (q.exponent*12) (CFSGTrialityGeckGoodSylow.original_goodSylowPrime q)
      P hP e.symm.toMonoidHom e.symm.surjective
  have hout : Nat.card (Outer D.Simple) ≤ 3*q.exponent := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGTrialityGeckOriginalOuterBound.original_outer_card_le_three_exponent q
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases hcut : 128 ≤ Nat.card X
  · have hf : q.exponent ≤ 2 :=
      PrimePowerProperIndexExponentBound.exponent_le q 4 (Nat.card X) 2 hsize (by omega)
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 2 Nat.card_pos (by omega)
    have hcost : MarkedC4.genRank G ≤ 27 := by omega
    have hb : 27 ≤ traceyPermutationGeneratorCeiling 128 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 128 1 7 27
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact hcost.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hcut))
  · have hf : q.exponent ≤ 1 :=
      PrimePowerProperIndexExponentBound.exponent_le q 4 (Nat.card X) 1 hsize (by omega)
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 Nat.card_pos (by omega)
    have hcost : MarkedC4.genRank G ≤ 14 := by omega
    have hb : 14 ≤ traceyPermutationGeneratorCeiling 32 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 14
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact hcost.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hminimum))

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G)=⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityAllDegreeOrdinary
