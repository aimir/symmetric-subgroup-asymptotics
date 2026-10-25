import SymmetricSubgroupAsymptotics.OriginalNonaffineDisplayedPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleSharpPairFamiliesAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary

/-! Original block consumers for all currently proved pair families.
The generating pair and sufficient index packet are filled internally
for the literal model selected by the SAME factor equivalence. No
simple-two-generation premise or model callback is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesBlockOrdinaryStep
open PrimitiveSocleRawStructure
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceyStrictlySmallerTransitiveActions

/-- Exactly the families for which this consumer uses an already proved
literal ordinary generating pair. This is not a completeness assertion. -/
def PairFamily : CFSG.Index → Prop
  | .alternating _ _ | .A _ _ _ _ | .B _ _ _ | .C _ _ _ _ | .D _ _ _ | .suzuki _ _ => True
  | _ => False

private theorem model_pair (j : CFSG.Index) (hj : PairFamily j)
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
are paid at every actual local degree at least 25 and every actual top.
The only induction assumption is on strictly smaller TRANSITIVE actions. -/
theorem genRank_le_ceiling (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hr : 25 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  have hpacket := CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn
  rcases hpacket with hpacket | hremaining
  · exact OriginalNonaffineDisplayedPairBlockOrdinaryStep.genRank_le_ceiling_of_model
      J block D e (model_pair j hj) hpacket i hr hbelow
  · exact (not_remaining j hj hremaining).elim

theorem exists_generating_finset (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hr : 25 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D j hj e i hr hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesBlockOrdinaryStep
