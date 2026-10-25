import SymmetricSubgroupAsymptotics.PrimitiveSocleModelRootStarOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationModels
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGClassicalSufficientSimpleIndexReduction

/-! All original type-D ranks in the one-factor ordinary tail. The same
actual model supplies its proved generating pair and root-star index.
Rank four consumes the already proved sufficient triality outer budget;
higher ranks consume the proved sharp outer bound. No group-classification
catalogue, global generation input, or scalar-fitting hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv D.Simple e.toEquiv
  have hroots : ∃ S : Finset (CFSG.Models.D r q),
      Subgroup.closure (S : Set (CFSG.Models.D r q)) = ⊤ ∧
        S.card ≤ (2*r)*q.exponent := by
    obtain ⟨S,hS,hcard⟩ := CFSGReduction.typeD_twoGenerated_of_index r q hr
    refine ⟨S,hS,hcard.trans ?_⟩
    simpa only [Nat.mul_one] using Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 (show 1 ≤ r by omega))
      (show 1 ≤ q.exponent from q.exponent_pos)
  have hstar : ∀ H : Subgroup (CFSG.Models.D r q), H ≠ ⊤ →
      q.order^(r-1) ≤ H.index :=
    CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r hr q
  have houter : ∀ ell : ℕ, LeastProperIndex (CFSG.Models.D r q) ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.D r q))) := by
    intro ell hell
    by_cases hfour : r = 4
    · subst r
      exact (CFSGReduction.typeD_four_sufficientSimpleIndexBudget q ell hell).2
    · have hellT := CFSGReduction.leastProperIndex_of_mulEquiv e.symm ell hell
      have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
        (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hellT.1
      exact SufficientOuterOrderBudget.of_sharp hell5
        (CFSGReduction.typeD_high_outer_card_le_log r (by omega) q ell hell)
  exact PrimitiveSocleModelRootStarOrdinaryTail.genRank_le_ceiling
    D hk q r (by omega) e hroots hstar houter hn

theorem exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk r hr q e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail
