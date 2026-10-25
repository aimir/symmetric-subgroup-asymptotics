import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTwiceQuadraticSylowTail
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGFFourCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The same original F4 positive Sylow and Heisenberg index supply
r=4 and a=24. This family consumer has no model generation callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleFFourOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGFFourE6OriginalProjection

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.F4 q) (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.F4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
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
  exact PrimitiveSocleOneFactorTwiceQuadraticSylowTail.genRank_le_ceiling
    D hk q 4 24 (by decide) (CFSGFFourOriginalGoodSylow.typeFFour_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective ell hell hfield houter hn

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.F4 q) (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk q e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleFFourOneFactorOrdinaryTail
