import SymmetricSubgroupAsymptotics.PrimitiveSocleFFourOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimePowerProperIndexExponentBound
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryQuadraticLeviIndex
/-! The whole F4 one-factor primitive ordinary branch. Actual
root-Sylow order, outer order and proper index bounds pay every field
through two exponent bands. No action census or pair premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleFFourAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGFFourE6OriginalProjection

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.F4 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleFFourOneFactorOrdinaryTail.genRank_le_ceiling D hk q e hlarge
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.F4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H,hH,hindex⟩ := hm.1
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hi : q.prime*q.order^4 ≤ Nat.card X :=
    ((CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index q H hH).trans_eq hindex).trans hdegree
  have hsize : 2*q.order^4 ≤ Nat.card X :=
    (Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans hi
  have hminimum : 128 ≤ Nat.card X := by
    by_cases hbinary : q.order=2
    · exact ((CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_levi_le_proper_index
        q hbinary H hH).trans_eq hindex).trans hdegree
    · have hq3 : 3 ≤ q.order := by
        have hh := CFSGTwistedAQuadraticTrace.order_two_le q
        omega
      have hp : 162 ≤ 2*q.order^4 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hq3 4)
      omega
  let P := originalPositiveSylow q.Field q.prime
  have hP : Nat.card P ∣ q.prime^(q.exponent*24) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGFFourE6OriginalFiniteBruhatCover.originalPositiveSylow_card_le q.Field q.prime
    rw [q.card_field] at hc
    change Nat.card P ≤ (q.prime^q.exponent)^24 at hc
    simpa only [pow_mul] using hc
  have hhead : MarkedC4.genRank D.Simple ≤ q.exponent*24+1 :=
    GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      q.prime (q.exponent*24) (CFSGFFourOriginalGoodSylow.typeFFour_goodSylowPrime q)
      P hP e.symm.toMonoidHom e.symm.surjective
  have hout : Nat.card (Outer D.Simple) ≤ 2*q.exponent := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGFFourE6OriginalOuterBound.typeFFour_outer_card_le_two_exponent q
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases hcut : 512 ≤ Nat.card X
  · have hf : q.exponent ≤ 2 :=
      PrimePowerProperIndexExponentBound.exponent_le q 4 (Nat.card X) 2 hsize (by omega)
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 2 Nat.card_pos (by omega)
    have hcost : MarkedC4.genRank G ≤ 51 := by omega
    have hb : 51 ≤ traceyPermutationGeneratorCeiling 512 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 512 1 9 51
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact hcost.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hcut))
  · have hf : q.exponent ≤ 1 :=
      PrimePowerProperIndexExponentBound.exponent_le q 4 (Nat.card X) 1 hsize (by omega)
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 Nat.card_pos (by omega)
    have hcost : MarkedC4.genRank G ≤ 26 := by omega
    have hb : 26 ≤ traceyPermutationGeneratorCeiling 128 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 128 1 7 26
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact hcost.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hminimum))

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.F4 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G)=⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleFFourAllDegreeOrdinary
