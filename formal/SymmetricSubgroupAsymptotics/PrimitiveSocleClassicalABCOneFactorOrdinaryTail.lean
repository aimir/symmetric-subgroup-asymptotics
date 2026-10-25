import SymmetricSubgroupAsymptotics.PrimitiveSocleModelPairOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGTypeAModelGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeASimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationModels
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticGenerationReduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleIndexReduction

/-! Whole original A/B/C families in the one-factor ordinary tail. Each
consumer uses the SAME literal model's proved generating pair and sharp
outer/index theorem. All original rank/small-field guards are retained.
No global generator, model callback, or permutation induction is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalABCOneFactorOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem typeA_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) (hs : r = 1 → 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e
    (CFSGReduction.typeA_twoGenerated r q hr hs) ?_ hn
  intro ell hell
  exact (CFSGReduction.typeA_simpleIndexBounds r q hr hs ell hell).2

theorem typeA_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) (hs : r = 1 → 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeA_genRank_le_ceiling D hk r q hr hs e hn)⟩

theorem typeB_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 3 ≤ r)
    (e : D.Simple ≃* CFSG.Models.B r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.B r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e
    (CFSGReduction.typeB_twoGenerated_of_index r q hr) ?_ hn
  intro ell hell
  exact (CFSGReduction.typeB_simpleIndexBounds r hr q ell hell).2

theorem typeB_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 3 ≤ r)
    (e : D.Simple ≃* CFSG.Models.B r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeB_genRank_le_ceiling D hk r q hr e hn)⟩

theorem typeC_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.C r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e
    (CFSGReduction.typeC_twoGenerated_of_index r q hr hs) ?_ hn
  intro ell hell
  exact (CFSGReduction.typeC_simpleIndexBounds r hr q hs ell hell).2

theorem typeC_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.C r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeC_genRank_le_ceiling D hk r q hr hs e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalABCOneFactorOrdinaryTail
