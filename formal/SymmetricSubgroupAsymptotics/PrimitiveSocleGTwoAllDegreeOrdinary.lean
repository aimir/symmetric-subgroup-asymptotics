import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! The whole G2 one-factor primitive ordinary branch. The actual
selected Sylow gives head 6f+1, the original outer group has order at
most 2f, and the literal proper index is at least 2q^2. Below the
existing infinite tail, two uniform exponent bands pay every field.
No finite action census or generating-pair premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGGTwoD4GeckOriginalProjection

private theorem twice_square_le_index (q : CFSG.PrimePower) (hs : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] (H : Subgroup (CFSG.Models.G2 q))
    (hH : H ≠ ⊤) : 2 * q.order^2 ≤ H.index := by
  by_cases hthree : q.order = 3
  · have hi := CFSGGTwoCharacteristicThreeMiddleIndex.typeGTwo_field_three_le_proper_index
      q hthree H hH
    simpa only [hthree, show 2*(3:ℕ)^2=18 by decide] using
      (show 18 ≤ H.index by omega)
  have hq4 : 4 ≤ q.order := by
    have hh := CFSGTwistedAQuadraticTrace.order_two_le q
    omega
  by_cases hp : q.prime = 3
  · have hi := CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index
      q hp hq4 H hH
    have hsq : 16 ≤ q.order^2 := Nat.pow_le_pow_left hq4 2
    omega
  · exact (Nat.mul_le_mul_right (q.order^2) q.prime_isPrime.two_le).trans
      (CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hp H hH)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hs : q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.G2 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleGTwoOneFactorOrdinaryTail.genRank_le_ceiling D hk q hs e hlarge
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.G2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H,hH,hindex⟩ := hm.1
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hn32 : 32 ≤ Nat.card X :=
    ((CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs H hH).trans_eq hindex).trans hdegree
  have hsize : 2*q.order^2 ≤ Nat.card X :=
    ((twice_square_le_index q hs H hH).trans_eq hindex).trans hdegree
  have hfield : 2^q.exponent ≤ q.order := Nat.pow_le_pow_left q.prime_isPrime.two_le _
  have hpow : 2^(2*q.exponent+1) ≤ Nat.card X := by
    calc
      _ = 2*(2^q.exponent)^2 := by rw [pow_add,pow_one,show 2*q.exponent=q.exponent*2 by omega,pow_mul]; ring
      _ ≤ 2*q.order^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfield 2)
      _ ≤ _ := hsize
  let P := originalPositiveSylow q.Field q.prime
  have hP : Nat.card P ∣ q.prime^(q.exponent*6) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGGTwoD4GeckFixedBruhatOrderUpper.originalPositiveSylow_card_le q.Field q.prime
    rw [q.card_field] at hc
    change Nat.card P ≤ (q.prime^q.exponent)^6 at hc
    simpa only [pow_mul] using hc
  have hhead : MarkedC4.genRank D.Simple ≤ q.exponent*6+1 :=
    GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      q.prime (q.exponent*6) (CFSGGTwoOriginalGoodSylow.typeGTwo_goodSylowPrime q)
      P hP e.symm.toMonoidHom e.symm.surjective
  have hout : Nat.card (Outer D.Simple) ≤ 2*q.exponent := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases h128 : 128 ≤ Nat.card X
  · have hf : q.exponent ≤ 4 := by
      by_contra hh
      have hp : 2048 ≤ 2^(2*q.exponent+1) :=
        Nat.pow_le_pow_right (by decide : 0<2) (show 11 ≤ 2*q.exponent+1 by omega)
      omega
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 3 Nat.card_pos (by omega)
    have h28 : MarkedC4.genRank G ≤ 28 := by omega
    have hb : 28 ≤ traceyPermutationGeneratorCeiling 128 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 128 1 7 28
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h28.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) h128))
  · have hf : q.exponent ≤ 2 := by
      by_contra hh
      have hp : 128 ≤ 2^(2*q.exponent+1) :=
        Nat.pow_le_pow_right (by decide : 0<2) (show 7 ≤ 2*q.exponent+1 by omega)
      omega
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 2 Nat.card_pos (by omega)
    have h15 : MarkedC4.genRank G ≤ 15 := by omega
    have hb : 15 ≤ traceyPermutationGeneratorCeiling 32 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 15
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h15.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn32))

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hs : q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.G2 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G)=⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q hs e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoAllDegreeOrdinary
