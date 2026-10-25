import SymmetricSubgroupAsymptotics.PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
import SymmetricSubgroupAsymptotics.CFSGExceptionalSufficientSimpleIndexReduction
import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare

/-! Actual simple-index packets for every alternating/Lie model, with
only literal Tits/sporadic tags left over. All inequalities concern the
same original model. Classification transports that packet, or the
remaining literal model witness, to the same actual nonabelian factor. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic
open PrimitiveSocleRawStructure CFSGReduction
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

theorem model_packet_or_remaining (i : CFSG.Index)
    [hfinite : Finite i.Model] [hsimple : IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model) :
    ModelSufficientSimpleIndexBounds i ∨ RemainingModel i := by
  rcases sufficientSimpleIndex_model_or_remaining_after_exceptional_E i hn with hb | hi
  · exact Or.inl hb
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn => exact hi.elim
    | A r q hr hs => exact hi.elim
    | B r q hr => exact hi.elim
    | C r q hr hs => exact hi.elim
    | D r q hr => exact hi.elim
    | E6 q => exact hi.elim
    | E7 q => exact hi.elim
    | E8 q => exact hi.elim
    | suzuki m hm => exact hi.elim
    | F4 q =>
      letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
      letI : Finite (CFSG.Models.F4 q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGFFourE6OriginalIndexSquare.original_index_square q.Field q.prime ell hell,
        CFSGFFourCompleteOuterBudget.typeFFour_sufficient_outer_budget q ell hell⟩
    | G2 q hs =>
      letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
      letI : Finite (CFSG.Models.G2 q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGGTwoOriginalIndexSquare.typeGTwo_index_square q hs ell hell,
        CFSGGTwoCompleteOuterBudget.typeGTwo_sufficient_outer_budget q hs ell hell⟩
    | twistedA r q hr hs =>
      letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := hsimple
      letI : Finite (CFSG.Models.TwistedA r q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt r hr q hs ell hell,
        CFSGTwistedAUnitaryCoordinates.twistedA_admissible_sufficient_outer_budget r hr q hs hn ell hell⟩
    | twistedD r q hr =>
      letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
      letI : Finite (CFSG.Models.TwistedD r q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGReduction.typeTwistedD_leastProperIndex_square_lt_card r q hr ell hell,
        CFSGReduction.typeTwistedD_sufficientOuterBudget r hr q hn ell hell⟩
    | twistedE6 q =>
      letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
      letI : Finite (CFSG.Models.TwistedE6 q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGTwistedE6GeckOriginalIndexSquare.original_index_square q ell hell,
        CFSGTwistedE6CompleteOuterBudget.typeTwistedE6_sufficient_outer_budget q ell hell⟩
    | trialityD4 q =>
      letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
      letI : Finite (CFSG.Models.TrialityD4 q) := hfinite
      left
      intro ell hell
      exact ⟨CFSGTrialityGeckOriginalIndexSquare.original_index_square q ell hell,
        CFSGTrialityCompleteOuterBudget.typeTriality_sufficient_outer_budget q ell hell⟩
    | reeG2 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := hsimple
      letI : Finite (CFSG.Models.ReeG2 m) := hfinite
      left
      intro ell hell
      exact ⟨CFSGReeGTwoOriginalIndexSquare.original_index_square m hm ell hell,
        CFSGReeGTwoCompleteOuterBudget.reeGTwo_sufficient_outer_budget m hm ell hell⟩
    | reeF4 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := hsimple
      letI : Finite (CFSG.Models.ReeF4 m) := hfinite
      left
      intro ell hell
      exact ⟨CFSGReeFFourOriginalIndexSquare.original_index_square m (by omega) ell hell,
        CFSGReeFFourCompleteOuterBudget.reeFFour_sufficient_outer_budget m (by omega) ell hell⟩
    | tits => exact Or.inr trivial
    | sporadic s => exact Or.inr trivial

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem factor_packet_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification) :
    (∀ ell : ℕ, LeastProperIndex D.Simple ell →
      ell^2 < Nat.card D.Simple ∧
        SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) ∨
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  obtain ⟨i, ⟨e⟩⟩ := hCFSG.classify D.Simple
  letI : Finite i.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative i.Model := by
    intro h
    exact D.noncommutative ((isMulCommutative_congr e).mpr h)
  rcases model_packet_or_remaining i hn with hb | hi
  · exact Or.inl (sufficientSimpleIndexBounds_of_mulEquiv e hb)
  · exact Or.inr ⟨i, hi, ⟨e⟩⟩

end SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic
