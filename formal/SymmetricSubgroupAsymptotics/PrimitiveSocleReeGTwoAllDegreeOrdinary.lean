import SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The complete positive-parameter ReeGTwo one-factor ordinary branch.
The actual selected source-Sylow and original outer bound pay the finite
field range left by the existing infinite tail. No pair or index callback
is supplied; the same original model and literal index are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoAllDegreeOrdinary
open PrimitiveSocleRawStructure CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoRootGeneratedNormal
open CFSGReeGTwoFixedCardinalitySylow CFSGReeGTwoOriginalGoodSylow

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeG2 m) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hlarge : 1024 ≤ Nat.card X
  · exact PrimitiveSocleReeGTwoOneFactorOrdinaryTail.genRank_le_ceiling D hk m hm e hlarge
  letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
  letI : Finite (originalModelFixed m) := fixedModel_finite m
  let q : CFSG.PrimePower :=
    { prime := 3, exponent := 2*m+1, prime_isPrime := by decide,
      exponent_pos := by omega }
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
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
  have hd := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hfieldN : 3^(2*m+1) ≤ Nat.card X := by
    simpa only [pow_one] using hfield.trans hd
  have hm2 : m ≤ 2 := by
    by_contra hh
    have hp : 2187 ≤ 3^(2*m+1) := Nat.pow_le_pow_right
      (by decide : 0<3) (show 7≤2*m+1 by omega)
    omega
  have hmin : 81 ≤ Nat.card X := by
    have hi := CFSGReeGTwoRectangularPermutationDegree.three_field_card_le_leastProperIndex
      m hm ell hellM
    have hp : 27 ≤ 3^(2*m+1) := Nat.pow_le_pow_right
      (by decide : 0<3) (show 3≤2*m+1 by omega)
    omega
  have hhead : MarkedC4.genRank D.Simple ≤ (2*m+1)*3+1 :=
    GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
      3 ((2*m+1)*3) (rootGenerated_goodSylowPrime m) P hP f hf
  have hout : Nat.card (Outer D.Simple) ≤ 2*(2*m+1) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReeGTwoOriginalOuterBound.outer_card_le m hm
  have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 3 Nat.card_pos (by omega)
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have h19 : MarkedC4.genRank G ≤ 19 := by omega
  have hb : 19 ≤ traceyPermutationGeneratorCeiling 81 :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 81 1 7 19
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h19.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hmin))

theorem exists_generating_finset (hk : D.factorCount = 1) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeG2 m) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk m hm e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoAllDegreeOrdinary
