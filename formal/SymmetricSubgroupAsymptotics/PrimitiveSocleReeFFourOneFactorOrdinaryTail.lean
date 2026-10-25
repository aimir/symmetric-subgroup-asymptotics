import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorLinearSylowTail
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original Ree F4 model for m>0 in the ordinary one-factor tail.
The selected positive Sylow is the actual image of the derived fixed
source's positive Sylow of cardinal q^12. The full central quotient is
retained. This file makes no assertion for the Tits parameter m=0. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourDerivedPositiveSylow CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourOriginalPositiveSylow

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
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
  exact PrimitiveSocleOneFactorLinearSylowTail.genRank_le_ceiling
    D hk q 1 12 (by decide) (CFSGReeFFourOriginalGoodSylow.original_goodSylowPrime m hm)
    P hP e.symm.toMonoidHom e.symm.surjective ell hell hfield houter hn

theorem exists_generating_finset (hk : D.factorCount = 1) (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk m hm e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOneFactorOrdinaryTail
