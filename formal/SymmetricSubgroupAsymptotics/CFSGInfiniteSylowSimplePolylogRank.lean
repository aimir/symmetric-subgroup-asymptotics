import SymmetricSubgroupAsymptotics.PrimitiveSimplePolylogRankTools
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic

/-! Actual source-Sylow data reused BEFORE the old one-factor scalar fit.
No factorCount=1, current-degree threshold or smaller-action hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGInfiniteSylowSimplePolylogRank
open PrimitiveSocleRawStructure PrimitiveSimplePolylogRankTools
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

namespace Unitary
open PrimitiveSocleRawStructure CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates
private theorem triangle_le_square (r : ℕ) (hr : 1 ≤ r) : r*(r+1)/2 ≤ r^2 := by
  have hh : r*(r+1) ≤ 2*r^2 := by nlinarith
  have hd : r*(r+1)/2 ≤ (2*r^2)/2 := Nat.div_le_div_right hh
  omega


theorem simple_rank
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r=2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnoncomm : ¬ IsMulCommutative (CFSG.Models.TwistedA r q) := by
    intro h
    apply D.noncommutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e x) (e y)
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ r ≤ ell :=
    twistedA_admissible_order_power_le_leastProperIndex r hr q hs ell hellM
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact twistedA_admissible_sufficient_outer_budget r hr q hs hnoncomm ell hellM
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hq : 3 ≤ q.order := by have hh := hs rfl; omega
    letI : Finite (fixedNaturalPullback 2 q) :=
      Finite.of_injective (pullbackMatrix 2 q) (CFSGTwistedA2UnipotentArrays.pullbackMatrix_two_injective q)
    letI : Finite (OriginalFixedA 2 q) :=
      Finite.of_surjective (pullbackSource 2 q) (pullbackSource_surjective 2 (by decide) q)
    let A := commutator (OriginalFixedA 2 q)
    let U := CFSGTwistedA2UnipotentArrays.originalUnipotent q
    have hUA : U ≤ A := CFSGTwistedA2UnipotentArrays.originalUnipotent_le_commutator q hq
    let P : Sylow q.prime A :=
      (CFSGTwistedA2UnipotentArrays.originalSylow q hq).subtype
        (CFSGTwistedA2UnipotentArrays.originalSylow_le_commutator q hq)
    have hcard : Nat.card P = q.order ^ 3 := by
      have he : Nat.card P = Nat.card U :=
        Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (CFSGTwistedA2UnipotentArrays.originalUnipotent_card q hq)
    have hP : Nat.card P ∣ q.prime ^ (q.exponent * 3) := by
      rw [hcard]
      change (q.prime ^ q.exponent) ^ 3 ∣ q.prime ^ (q.exponent * 3)
      rw [pow_mul]
    let f : A →* D.Simple := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
    have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    exact rank_le_of_sylow
      q 2 3 ell (by decide)
      (CFSGTwistedA2UnipotentArrays.originalDerived_goodSylowPrime q hq)
      P hP f hf hfield
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    letI : Finite (Fixed (s+3) q) := originalFixed_finite q (s+3) (by omega)
    let A := commutator (Fixed (s+3) q)
    let U := originalUnipotent (s+3) q
    have hUA : U ≤ A := originalUnipotent_le_derived q s
    let P : Sylow q.prime A :=
      (originalSylow q (s+3) (by omega)).subtype (originalSylow_le_derived q s)
    have hcard : Nat.card P = q.order ^ ((s+3)*(s+4)/2) := by
      have he : Nat.card P = Nat.card U :=
        Nat.card_congr (U.subgroupOfEquivOfLe hUA).toEquiv
      exact he.trans (original_unipotent_card q (s+3) (by omega))
    have hP : Nat.card P ∣ q.prime ^ (q.exponent * ((s+3)*(s+4)/2)) := by
      rw [hcard]
      change (q.prime ^ q.exponent) ^ ((s+3)*(s+4)/2) ∣
        q.prime ^ (q.exponent * ((s+3)*(s+4)/2))
      rw [pow_mul]
    let f : A →* D.Simple := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
    have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    apply rank_le_of_sylow
      q (s+3) ((s+3)*(s+4)/2) ell ?_
      (originalDerived_goodSylowPrime q s) P hP f hf hfield
    exact (triangle_le_square (s+3) (by omega)).trans (by omega)

end Unitary

namespace FFour
open PrimitiveSocleRawStructure CFSGFFourE6OriginalProjection
theorem simple_rank (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.F4 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.F4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H, hH, he⟩ := hellM.1
  have hfield : q.order ^ 4 ≤ ell := by
    calc
      q.order ^ 4 ≤ q.prime * q.order ^ 4 :=
        Nat.le_mul_of_pos_left _ q.prime_isPrime.pos
      _ ≤ H.index := CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index q H hH
      _ = ell := he
  let P := originalPositiveSylow q.Field q.prime
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 24) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGFFourE6OriginalFiniteBruhatCover.originalPositiveSylow_card_le q.Field q.prime
    rw [q.card_field] at hc
    change Nat.card P ≤ (q.prime ^ q.exponent) ^ 24 at hc
    simpa only [pow_mul] using hc
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGFFourCompleteOuterBudget.typeFFour_sufficient_outer_budget q ell hellM
  exact rank_le_of_sylow
    q 4 24 ell (by decide) (CFSGFFourOriginalGoodSylow.typeFFour_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective hfield

end FFour

namespace GTwo
open PrimitiveSocleRawStructure CFSGGTwoD4GeckOriginalProjection
private theorem field_square_le_index (q : CFSG.PrimePower) (hsmall : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] [Finite (CFSG.Models.G2 q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.G2 q) ell) : q.order ^ 2 ≤ ell := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  by_cases hthree : q.order = 3
  · have hcard : 3 ^ 12 ≤ Nat.card (CFSG.Models.G2 q) := by
      have hh := original_order_lower q.Field
      simpa only [q.card_field, hthree] using hh
    have hdvd := SimpleLeastIndexStrictOrdinaryGenerators.card_dvd_factorial
      (CFSG.Models.G2 q) ell hell
    have hle := Nat.le_of_dvd (Nat.factorial_pos ell) hdvd
    have hnine : 9 ≤ ell := by
      by_contra hn
      have hf : ell.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le (by omega)
      norm_num only [show (8 : ℕ).factorial = 40320 by decide] at hf
      norm_num only [show (3 : ℕ)^12 = 531441 by decide] at hcard
      omega
    simpa only [hthree, show (3 : ℕ)^2 = 9 by decide] using hnine
  · obtain ⟨H, hH, he⟩ := hell.1
    by_cases hchar : q.prime = 3
    · have hq4 : 4 ≤ q.order := by omega
      have hi := CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index
        q hchar hq4 H hH
      have hsquare : 2 ≤ q.order ^ 2 :=
        (by decide : 2 ≤ (4 : ℕ)^2).trans (Nat.pow_le_pow_left hq4 2)
      have hbound : q.order ^ 2 ≤ 3 * (q.order ^ 2 - 1) := by omega
      exact hbound.trans (hi.trans_eq he)
    · have hi := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hchar H hH
      exact (Nat.le_mul_of_pos_left _ q.prime_isPrime.pos).trans (hi.trans_eq he)


theorem simple_rank (q : CFSG.PrimePower)
    (hsmall : q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.G2 q)

    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.G2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ 2 ≤ ell := field_square_le_index q hsmall ell hellM
  let P := originalPositiveSylow q.Field q.prime
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 6) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGGTwoD4GeckFixedBruhatOrderUpper.originalPositiveSylow_card_le q.Field q.prime
    rw [q.card_field] at hc
    change Nat.card P ≤ (q.prime ^ q.exponent) ^ 6 at hc
    simpa only [pow_mul] using hc
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGGTwoCompleteOuterBudget.typeGTwo_sufficient_outer_budget q hsmall ell hellM
  exact rank_le_of_sylow
    q 2 6 ell (by decide) (CFSGGTwoOriginalGoodSylow.typeGTwo_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective hfield

end GTwo

namespace TwistedESix
open PrimitiveSocleRawStructure CFSGTwistedE6GeckOriginalProjection
theorem simple_rank (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedE6 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  obtain ⟨H, hH, he⟩ := hellM.1
  have hfield : q.order ^ 10 ≤ ell := by
    calc
      q.order ^ 10 ≤ q.prime * q.order ^ 10 :=
        Nat.le_mul_of_pos_left _ q.prime_isPrime.pos
      _ ≤ H.index := CFSGTwistedE6HeisenbergIndex.prime_mul_order_ten_le_proper_index q H hH
      _ = ell := he
  have hdegree : 1024 ≤ Nat.card X := by
    have hindex : 2048 ≤ ell := he ▸
      CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q H hH
    have hle := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    omega
  let P := originalPositiveSylow q
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 48) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGTwistedE6GeckOriginalFiniteBruhatCover.originalPositiveSylow_card_le q
    change Nat.card P ≤ (q.prime ^ q.exponent) ^ 48 at hc
    simpa only [pow_mul] using hc
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGTwistedE6CompleteOuterBudget.typeTwistedE6_sufficient_outer_budget q ell hellM
  exact rank_le_of_sylow
    q 10 48 ell (by decide)
    (CFSGTwistedE6OriginalGoodSylow.typeTwistedE6_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective hfield

end TwistedESix

namespace Triality
open PrimitiveSocleRawStructure CFSGTrialityGeckOriginalRootFamily
theorem simple_rank (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ 2 ≤ ell := by
    have hcube := CFSGTrialityGeckPermutationDegree.order_cube_le_twice_leastProperIndex q ell hellM
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hscale : 2 * q.order ^ 2 ≤ q.order ^ 3 := by
      calc
        2 * q.order ^ 2 ≤ q.order * q.order ^ 2 := Nat.mul_le_mul_right _ hq2
        _ = q.order ^ 3 := by ring
    omega
  let P := originalSylow q
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 12) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGTrialityGeckOriginalFiniteBruhatCover.originalSylow_card_le q
    change Nat.card P ≤ (q.prime ^ q.exponent) ^ 12 at hc
    simpa only [pow_mul] using hc
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGTrialityCompleteOuterBudget.typeTriality_sufficient_outer_budget q ell hellM
  exact rank_le_of_sylow
    q 2 12 ell (by decide) (CFSGTrialityGeckGoodSylow.original_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective hfield

end Triality

namespace ReeGTwo
open PrimitiveSocleRawStructure CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoRootGeneratedNormal
open CFSGReeGTwoFixedCardinalitySylow CFSGReeGTwoOriginalGoodSylow
theorem simple_rank (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeG2 m)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
  letI : Finite (originalModelFixed m) := fixedModel_finite m
  let q : CFSG.PrimePower :=
    { prime := 3, exponent := 2*m+1, prime_isPrime := by decide,
      exponent_pos := by omega }
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ 1 ≤ ell := by
    simpa only [pow_one] using
      CFSGReeGTwoPermutationDegree.field_card_le_leastProperIndex m hm ell hellM
  let H := fixedRootGenerated m
  let P : Sylow 3 H := (fixedPositiveSylow m).subtype (positive_le_generated m)
  have hcard : Nat.card P = (3^(2*m+1))^3 := by
    have he : Nat.card P = Nat.card (fixedPositiveGroup m) :=
      Nat.card_congr ((fixedPositiveGroup m).subgroupOfEquivOfLe (positive_le_generated m)).toEquiv
    exact he.trans (fixedPositiveGroup_card m)
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 3) := by
    rw [hcard]
    change (3^(2*m+1))^3 ∣ 3^((2*m+1)*3)
    rw [pow_mul]
  let f : H →* D.Simple := e.symm.toMonoidHom.comp (rootReeHom m hm)
  have hf : Function.Surjective f := e.symm.surjective.comp (rootReeHom_surjective m hm)
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReeGTwoCompleteOuterBudget.reeGTwo_sufficient_outer_budget m hm ell hellM
  exact rank_le_of_sylow
    q 1 3 ell (by decide) (rootGenerated_goodSylowPrime m)
    P hP f hf hfield

end ReeGTwo

namespace ReeFFour
open PrimitiveSocleRawStructure CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourDerivedPositiveSylow CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourOriginalPositiveSylow
theorem simple_rank (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv D.Simple e.toEquiv
  let q : CFSG.PrimePower :=
    { prime := 2, exponent := 2*m+1, prime_isPrime := Nat.prime_two,
      exponent_pos := by omega }
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (commutator (originalModelFixed m)) :=
    Finite.of_injective (derivedAmbientHom m) (derivedAmbientHom_injective m)
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ 1 ≤ ell := by
    simpa only [pow_one] using
      CFSGReeFFourPermutationDegree.order_le_leastProperIndex m hm ell hellM
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
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReeFFourCompleteOuterBudget.reeFFour_sufficient_outer_budget m hm ell hellM
  exact rank_le_of_sylow
    q 1 12 ell (by decide) (CFSGReeFFourOriginalGoodSylow.original_goodSylowPrime m hm)
    P hP e.symm.toMonoidHom e.symm.surjective hfield

end ReeFFour

end SymmetricSubgroupAsymptotics.CFSGInfiniteSylowSimplePolylogRank
