import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootStarOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationModels
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDHigherRankSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A genuine original-model family consumer of the one-factor ordinary
tail. The displayed type-D generating pair, original root-star index
bound, and original outer bound are all proved model theorems. The
classification isomorphism remains literal; no global simple generation,
simple-index, or permutation-generator input is added. Rank four keeps
its separate actual triality outer boundary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDOneFactorOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (hr : 5 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv D.Simple e.toEquiv
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm
    (CFSGReduction.typeD_twoGenerated_of_index r q (by omega))
  have hcardRoot : S.card ≤ (2*r)*q.exponent := by
    have hh : (2 : ℕ) ≤ (2*r)*q.exponent := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 (show 1 ≤ r by omega))
        (show 1 ≤ q.exponent from q.exponent_pos)
    exact hcard.trans hh
  have hstar : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(r-1) ≤ H.index := by
    intro H hH
    have hmap : H.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hH
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index
      r (by omega) q (H.map e.toMonoidHom) hmap
    have hidx : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
    exact hh.trans_eq hidx
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    apply SufficientOuterOrderBudget.of_sharp hell5
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReduction.typeD_high_outer_card_le_log r hr q ell
      (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  exact PrimitiveSocleOneFactorRootStarOrdinaryTail.genRank_le_ceiling
    D hk q r (by omega) S hS hcardRoot hstar ell hell houter hn

theorem exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (hr : 5 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk r hr q e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDOneFactorOrdinaryTail
