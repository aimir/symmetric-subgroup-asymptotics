import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A literal model isomorphism transports its displayed pair and its sharp
outer/index theorem to the SAME original simple factor. Named-family
consumers prove both facts internally; no global model callback is installed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleModelPairOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) {M : Type} [Group M]

theorem genRank_le_ceiling_of_outer_budget (hk : D.factorCount = 1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hbudget : ∀ ell : ℕ, LeastProperIndex M ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hS,hcard⟩ := hpair
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set M)) = ⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hUcard : U.card ≤ 2 := Finset.card_image_le.trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact hbudget ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  exact PrimitiveSocleOneFactorPairOrdinaryTail.genRank_le_ceiling
    D hk U hU hUcard ell hell houter hn

theorem genRank_le_ceiling (hk : D.factorCount = 1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hsharp : ∀ ell : ℕ, LeastProperIndex M ell →
      (Nat.card (Outer M) : ℝ) ≤ 3*Real.logb 2 ell)
    (hn : 32 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  apply genRank_le_ceiling_of_outer_budget D hk e hpair ?_ hn
  intro ell hell
  have hellT := CFSGReduction.leastProperIndex_of_mulEquiv e.symm ell hell
  have hell5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hellT.1
  exact SufficientOuterOrderBudget.of_sharp hell5 (hsharp ell hell)

theorem exists_generating_finset (hk : D.factorCount = 1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hsharp : ∀ ell : ℕ, LeastProperIndex M ell →
      (Nat.card (Outer M) : ℝ) ≤ 3*Real.logb 2 ell)
    (hn : 32 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk e hpair hsharp hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleModelPairOrdinaryTail
