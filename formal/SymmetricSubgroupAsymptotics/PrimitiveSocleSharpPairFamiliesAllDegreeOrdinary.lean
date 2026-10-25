import SymmetricSubgroupAsymptotics.PrimitiveSocleModelSharpPairAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalABCOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound

/-! Complete original A/B/C, Suzuki and alternating one-factor ordinary
consumers at every degree. Each family supplies its literal pair and
proved sharp outer bound; the shared small-degree theorem is arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSharpPairFamiliesAllDegreeOrdinary
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem typeA_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) (hs : r = 1 → 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A r q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelSharpPairAllDegreeOrdinary.genRank_le_ceiling D hk e
    (CFSGReduction.typeA_twoGenerated r q hr hs) ?_
  intro ell hell
  exact (CFSGReduction.typeA_simpleIndexBounds r q hr hs ell hell).2

theorem typeA_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) (hs : r = 1 → 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A r q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeA_genRank_le_ceiling D hk r q hr hs e)⟩

theorem typeB_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 3 ≤ r)
    (e : D.Simple ≃* CFSG.Models.B r q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.B r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelSharpPairAllDegreeOrdinary.genRank_le_ceiling D hk e
    (CFSGReduction.typeB_twoGenerated_of_index r q hr) ?_
  intro ell hell
  exact (CFSGReduction.typeB_simpleIndexBounds r hr q ell hell).2

theorem typeB_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 3 ≤ r)
    (e : D.Simple ≃* CFSG.Models.B r q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeB_genRank_le_ceiling D hk r q hr e)⟩

theorem typeC_genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.C r q) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C r q) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelSharpPairAllDegreeOrdinary.genRank_le_ceiling D hk e
    (CFSGReduction.typeC_twoGenerated_of_index r q hr hs) ?_
  intro ell hell
  exact (CFSGReduction.typeC_simpleIndexBounds r hr q hs ell hell).2

theorem typeC_exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.C r q) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (typeC_genRank_le_ceiling D hk r q hr hs e)⟩

theorem suzuki_genRank_le_ceiling (hk : D.factorCount = 1)
    (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.Suzuki m) := Finite.of_equiv D.Simple e.toEquiv
  apply PrimitiveSocleModelSharpPairAllDegreeOrdinary.genRank_le_ceiling D hk e
    (CFSGSuzukiGeneration.suzuki_twoGenerated m hm) ?_
  intro ell hell
  exact (CFSGSuzukiOuterBound.simpleIndexBounds m hm ell hell).2

theorem suzuki_exists_generating_finset (hk : D.factorCount = 1)
    (m : ℕ) (hm : 1 ≤ m) (e : D.Simple ≃* CFSG.Models.Suzuki m)
    :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (suzuki_genRank_le_ceiling D hk m hm e)⟩

theorem alternating_genRank_le_ceiling (hk : D.factorCount=1)
    (n : ℕ) (hn : 5≤n) (e : D.Simple ≃* alternatingGroup (Fin n)) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  apply PrimitiveSocleModelSharpPairAllDegreeOrdinary.genRank_le_ceiling D hk e ?_ ?_
  · obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=alternatingGroup (Fin n))
    exact ⟨S,hgen,hS.le.trans (CFSGAlternatingGeneration.genRank_le_two n hn)⟩
  · intro ell hell
    exact (CFSGAlternatingOuterBound.simpleIndexBounds n hn ell hell).2

theorem alternating_exists_generating_finset (hk : D.factorCount=1)
    (n : ℕ) (hn : 5≤n) (e : D.Simple ≃* alternatingGroup (Fin n)) :
    ∃ U : Finset G, Subgroup.closure (U:Set G)=⊤ ∧
      U.card≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨U,hgen,hU.le.trans (alternating_genRank_le_ceiling D hk n hn e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleSharpPairFamiliesAllDegreeOrdinary
