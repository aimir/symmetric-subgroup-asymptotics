import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The complete positive-parameter ReeFFour one-factor ordinary branch.
The actual selected source-Sylow and original outer bound pay the finite
field range left by the existing infinite tail. No pair or index callback
is supplied; the same original model and literal index are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourDerivedPositiveSylow CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourOriginalPositiveSylow

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleReeFFourOneFactorOrdinaryTail.genRank_le_ceiling D hk m hm e hlarge
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv D.Simple e.toEquiv
  let q : CFSG.PrimePower :=
    { prime := 2, exponent := 2*m+1, prime_isPrime := Nat.prime_two,
      exponent_pos := by omega }
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (commutator (originalModelFixed m)) :=
    Finite.of_injective (derivedAmbientHom m) (derivedAmbientHom_injective m)
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  let P := reePositiveSylow m hm
  let Q := derivedPositiveSylow m hm
  have hcard : Nat.card P ≤ (2^(2*m+1))^12 := by
    have hPQ : Nat.card P ≤ Nat.card Q := by
      change Nat.card ((Q : Subgroup (commutator (originalModelFixed m))).map
        (derivedReeHom m)) ≤ Nat.card Q
      exact Nat.card_le_card_of_surjective
        ((derivedReeHom m).subgroupMap (Q : Subgroup (commutator (originalModelFixed m))))
        ((derivedReeHom m).subgroupMap_surjective _)
    exact hPQ.trans_eq (CFSGReeFFourOriginalOrderLower.derivedPositiveSylow_card m hm)
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 12) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    simpa only [pow_mul] using hcard
  obtain ⟨H,hH,hindex⟩ := hellM.1
  have hd := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hi : (2^(2*m+1)-1)*2^(m+1) ≤ Nat.card X :=
    ((CFSGReeFFourMiddleSuzukiIndex.middle_suzuki_le_proper_index m hm H hH).trans_eq hindex).trans hd
  have hm2 : m ≤ 2 := by
    by_contra hh
    have hp : 128 ≤ 2^(2*m+1) := Nat.pow_le_pow_right
      (by decide : 0<2) (show 7 ≤ 2*m+1 by omega)
    have hp' : 16 ≤ 2^(m+1) := Nat.pow_le_pow_right
      (by decide : 0<2) (show 4 ≤ m+1 by omega)
    have hprod : 2032 ≤ (2^(2*m+1)-1)*2^(m+1) :=
      Nat.mul_le_mul (show 127 ≤ 2^(2*m+1)-1 by omega) hp'
    omega
  have hhead : MarkedC4.genRank D.Simple ≤ (2*m+1)*12+1 := by
    exact GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      2 ((2*m+1)*12) (CFSGReeFFourOriginalGoodSylow.original_goodSylowPrime m hm)
      P hP e.symm.toMonoidHom e.symm.surjective
  have hout : Nat.card (Outer D.Simple) ≤ 2*m+1 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReeFFourOriginalOuterBound.outer_card_le m hm
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases hone : m=1
  · have hmin : 109 ≤ Nat.card X := by
      have hm1 : LeastProperIndex (CFSG.Models.ReeF4 1) ell :=
        (congrArg (fun t : ℕ => LeastProperIndex (CFSG.Models.ReeF4 t) ell) hone).mp hellM
      letI : IsSimpleGroup (CFSG.Models.ReeF4 1) :=
        (congrArg (fun t : ℕ => IsSimpleGroup (CFSG.Models.ReeF4 t)) hone).mp
          (inferInstance : IsSimpleGroup (CFSG.Models.ReeF4 m))
      obtain ⟨K,hK,hKi⟩ := hm1.1
      exact ((CFSGReeFFourFieldEightPrimeIndex.proper_index_le K hK).trans_eq hKi).trans hd
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 Nat.card_pos (by omega)
    have h38 : MarkedC4.genRank G ≤ 38 := by omega
    have hb : 38 ≤ traceyPermutationGeneratorCeiling 109 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 109 1 7 38
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h38.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hmin))
  · have he : m=2 := by omega
    have hmin : 248 ≤ Nat.card X := by simpa only [he] using hi
    have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 :=
      SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 2 Nat.card_pos (by omega)
    have h63 : MarkedC4.genRank G ≤ 63 := by omega
    have hb : 63 ≤ traceyPermutationGeneratorCeiling 248 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 248 1 8 63
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h63.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hmin))

theorem exists_generating_finset (hk : D.factorCount = 1) (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk m hm e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourAllDegreeOrdinary
