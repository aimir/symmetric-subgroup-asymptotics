import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorLinearSylowTail
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original triality model has an actual positive Sylow of
cardinal at most q^12. Its q^3 <= 2*ell bound implies q^2 <= ell,
and the selected-Sylow linear-ratio theorem pays the ordinary tail. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGTrialityGeckOriginalRootFamily

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
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
  exact PrimitiveSocleOneFactorLinearSylowTail.genRank_le_ceiling
    D hk q 2 12 (by decide) (CFSGTrialityGeckGoodSylow.original_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective ell hell hfield houter hn

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk q e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityOneFactorOrdinaryTail
