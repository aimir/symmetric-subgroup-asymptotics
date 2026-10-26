import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsActualOrdinaryPacket
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallMultipleStrictOrdinary

/-! Every actual Tits primitive ordinary row, using only strict-smaller
TRANSITIVE induction for the multifactor branch. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTitsCompleteOrdinary
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (e : D.Simple ≃* CFSG.Index.tits.Model)
    (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have h14 := PrimitiveSocleTitsActualOrdinaryPacket.least_index_fourteen_le D e ell hell
  obtain ⟨horder,houter⟩ := PrimitiveSocleTitsActualOrdinaryPacket.packet D e ell hell
  by_cases hk : D.factorCount=1
  · have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    exact PrimitiveSocleOneFactorFourOrdinaryFromTwelve.genRank_le_ceiling D hk
      (PrimitiveSocleTitsActualOrdinaryPacket.simple_genRank_le_four D e)
      ell hell houter (by omega)
  · have hk2 : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
    have hdegree := primitiveSocle_power_le_degree (by omega : 5 ≤ ell) horder (D.degreeForm hell)
    have hp := (Nat.pow_le_pow_right (by omega : 0 < ell) hk2).trans hdegree
    have h32 : 32 ≤ Nat.card X := by nlinarith only [hp,h14]
    exact PrimitiveSocleSmallMultipleStrictOrdinary.genRank_le_ceiling
      D ell hbelow hell hk2 horder h32 houter

theorem exists_generating_finset (e : D.Simple ≃* CFSG.Index.tits.Model)
    (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling D e hbelow)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTitsCompleteOrdinary
