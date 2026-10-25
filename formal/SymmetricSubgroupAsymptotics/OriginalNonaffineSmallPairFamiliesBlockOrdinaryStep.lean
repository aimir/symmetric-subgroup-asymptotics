import SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesBlockOrdinaryStep

/-! Actual pair-family consumers at every local degree >=10. The same
indexed model witness supplies its proved ordinary pair and sufficient
index packet internally. Local degrees below10 remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep
open PrimitiveSocleRawStructure
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceyStrictlySmallerTransitiveActions
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

theorem model_pair_of_family (j : CFSG.Index) (hj : PairFamily j)
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

private theorem not_remaining (j : CFSG.Index) (hj : PairFamily j) : ¬ RemainingModel j := by
  cases j <;> simp_all only [PairFamily,RemainingModel,not_false_eq_true]

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

/-- All alternating, untwisted classical A/B/C/D and Suzuki local factors
are paid at every actual local degree at least 10 and every actual top.
The only induction assumption is on strictly smaller TRANSITIVE actions. -/
theorem genRank_le_ceiling (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hr : 10 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  have hpacket := CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn
  rcases hpacket with hpacket | hremaining
  · exact OriginalNonaffineSmallPairBlockOrdinaryStep.genRank_le_ceiling_of_model
      J block D e (model_pair_of_family j hj) hpacket i hr hbelow
  · exact (not_remaining j hj hremaining).elim

theorem exists_generating_finset (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hr : 10 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D j hj e i hr hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep
