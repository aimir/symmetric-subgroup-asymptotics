import SymmetricSubgroupAsymptotics.PrimitiveSocleModelPairOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGSuzukiTwoGeneration
import SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound

/-! The whole original Suzuki family in the one-factor ordinary tail.
Its displayed pair and sharp outer/index bound are both proved in the
same pinned matrix model. No generation or permutation callback is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiOneFactorOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.Suzuki m) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e
    (CFSGSuzukiGeneration.suzuki_twoGenerated m hm) ?_ hn
  intro ell hell
  exact (CFSGSuzukiOuterBound.simpleIndexBounds m hm ell hell).2

theorem exists_generating_finset (hk : D.factorCount = 1)
    (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    (hn : 32 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk m hm e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiOneFactorOrdinaryTail
