import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorSylowOrderOrdinaryTail
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The whole original twisted E6 family in the one-factor ordinary
generator bound. The same original positive Sylow has cardinal at most
q^48, while the actual Heisenberg subgroup forces proper index at least
p*q^10 and hence at least 2048. No separate degree threshold is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6OneFactorOrdinaryGenerators
open PrimitiveSocleRawStructure CFSGTwistedE6GeckOriginalProjection

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedE6 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
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
  exact PrimitiveSocleOneFactorSylowOrderOrdinaryTail.genRank_le_ceiling
    D hk q 10 48 (by decide)
    (CFSGTwistedE6OriginalGoodSylow.typeTwistedE6_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective ell hell hfield houter hdegree

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6OneFactorOrdinaryGenerators
