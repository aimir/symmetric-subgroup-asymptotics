import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedMultiplePairOrdinary
import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesBlockOrdinaryStep

/-! Complete primitive ordinary bounds for every proved pair family,
with arbitrary socle multiplicity and the full original quotient.
The genuine model pair and index packet are filled internally. Only
strictly smaller transitive induction is used in the infinite range. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSoclePairFamiliesCompleteOrdinary
open PrimitiveSocleRawStructure
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceyStrictlySmallerTransitiveActions

theorem model_generating_pair (j : CFSG.Index) (hj : PairFamily j)
    [hfinite : Finite j.Model] [hsimple : IsSimpleGroup j.Model] :
    ∃ S : Finset j.Model, Subgroup.closure (S : Set j.Model) = ⊤ ∧ S.card ≤ 2 := by
  cases j with
  | alternating m hm =>
    obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := alternatingGroup (Fin m))
    exact ⟨S,hgen,hS.le.trans (CFSGAlternatingGeneration.genRank_le_two m hm)⟩
  | A r q hr hs => exact CFSGReduction.typeA_twoGenerated r q hr hs
  | B r q hr =>
    letI : Finite (CFSG.Models.B r q) := hfinite
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    exact CFSGReduction.typeB_twoGenerated_of_index r q hr
  | C r q hr hs =>
    letI : Finite (CFSG.Models.C r q) := hfinite
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    exact CFSGReduction.typeC_twoGenerated_of_index r q hr hs
  | D r q hr =>
    letI : Finite (CFSG.Models.D r q) := hfinite
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    exact CFSGReduction.typeD_twoGenerated_of_index r q hr
  | suzuki m hm => exact CFSGSuzukiGeneration.suzuki_twoGenerated m hm
  | cyclic p hp => exact hj.elim
  | E6 q => exact hj.elim
  | E7 q => exact hj.elim
  | E8 q => exact hj.elim
  | F4 q => exact hj.elim
  | G2 q hs => exact hj.elim
  | twistedA r q hr hs => exact hj.elim
  | twistedD r q hr => exact hj.elim
  | twistedE6 q => exact hj.elim
  | trialityD4 q => exact hj.elim
  | reeG2 m hm => exact hj.elim
  | reeF4 m hm => exact hj.elim
  | tits => exact hj.elim
  | sporadic s => exact hj.elim

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hnot : ¬ RemainingModel j := by
    cases j <;> simp_all only [PairFamily,RemainingModel,not_false_eq_true]
  have hpacket := CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn
  rcases hpacket with hpacket | hremaining
  · have hpair := model_generating_pair j hj
    by_cases hk : D.factorCount=1
    · apply PrimitiveSocleSufficientPairAllDegreeOrdinary.genRank_le_ceiling D hk e hpair
      intro ell hell
      exact (hpacket ell hell).2
    · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
      have hactual := CFSGReduction.sufficientSimpleIndexBounds_of_mulEquiv e hpacket ell hell
      have hsimple : MarkedC4.genRank D.Simple ≤ 2 := by
        rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
        obtain ⟨S,hS,hcard⟩ := hpair
        exact (MarkedC4.genRank_le hS).trans hcard
      exact PrimitiveSocleBoundedMultiplePairOrdinary.genRank_le_ceiling
        D ell hbelow hell (by have hp := D.factorCount_pos; omega) hactual.1 hactual.2 hsimple
  · exact (hnot hremaining).elim

theorem exists_generating_finset (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hS,hcard.le.trans (genRank_le_ceiling D j hj e hbelow)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSoclePairFamiliesCompleteOrdinary
