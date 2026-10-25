import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootStarOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Transport actual root-generator, root-star, and outer-order model
facts along the literal classification isomorphism. This is a shared
model adapter, not a declaration that any model satisfies those facts.
Named-family consumers supply all three from their proved theorems. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleModelRootStarOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) {M : Type} [Group M]

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 2 ≤ r) (e : D.Simple ≃* M)
    (hroots : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧
      S.card ≤ (2*r)*q.exponent)
    (hstar : ∀ H : Subgroup M, H ≠ ⊤ → q.order^(r-1) ≤ H.index)
    (houter : ∀ ell : ℕ, LeastProperIndex M ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hS,hcard⟩ := hroots
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set M)) = ⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hUcard : U.card ≤ (2*r)*q.exponent := Finset.card_image_le.trans hcard
  have hstarT : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(r-1) ≤ H.index := by
    intro H hH
    have hmap : H.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hH
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hstar (H.map e.toMonoidHom) hmap
    have hidx : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
    exact hh.trans_eq hidx
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have houterT : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact houter ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  exact PrimitiveSocleOneFactorRootStarOrdinaryTail.genRank_le_ceiling
    D hk q r hr U hU hUcard hstarT ell hell houterT hn

theorem exists_generating_finset (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 2 ≤ r) (e : D.Simple ≃* M)
    (hroots : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧
      S.card ≤ (2*r)*q.exponent)
    (hstar : ∀ H : Subgroup M, H ≠ ⊤ → q.order^(r-1) ≤ H.index)
    (houter : ∀ ell : ℕ, LeastProperIndex M ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q r hr e hroots hstar houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleModelRootStarOrdinaryTail
