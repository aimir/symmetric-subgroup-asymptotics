import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalABCOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleFFourOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6OneFactorOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOneFactorOrdinaryTail

/-! Actual one-factor large primitive ordinary-generator reduction.
Every original Lie family and the alternating family is dispatched to
its proved model consumer along the same classification isomorphism.
Only literal Tits/sporadic tags survive. This is not a proof of those
residual models or of the global permutation-generator theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction

def RemainingModel : CFSG.Index → Prop
  | .tits | .sporadic _ => True
  | _ => False

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (hk : D.factorCount = 1)
    (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) ∨
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  obtain ⟨i, ⟨e⟩⟩ := hCFSG.classify D.Simple
  cases i with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (D.noncommutative ((isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm =>
    have hpair : CFSGGeneration.TwoGenerated (alternatingGroup (Fin m)) := by
      obtain ⟨a, ha⟩ := CFSGAlternatingGeneration.exists_generating_tuple m hm
      exact CFSGGeneration.of_generating_family a ha (by simp)
    exact Or.inl (PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e hpair
      (fun ell hell => (CFSGAlternatingOuterBound.simpleIndexBounds m hm ell hell).2)
      (by omega))
  | A r q hr hs =>
    exact Or.inl (PrimitiveSocleClassicalABCOneFactorOrdinaryTail.typeA_genRank_le_ceiling
      D hk r q hr hs e (by omega))
  | B r q hr =>
    exact Or.inl (PrimitiveSocleClassicalABCOneFactorOrdinaryTail.typeB_genRank_le_ceiling
      D hk r q hr e (by omega))
  | C r q hr hs =>
    exact Or.inl (PrimitiveSocleClassicalABCOneFactorOrdinaryTail.typeC_genRank_le_ceiling
      D hk r q hr hs e (by omega))
  | D r q hr =>
    exact Or.inl (PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail.genRank_le_ceiling
      D hk r hr q e (by omega))
  | E6 q =>
    exact Or.inl (PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE6_genRank_le_ceiling D hk q e)
  | E7 q =>
    exact Or.inl (PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE7_genRank_le_ceiling D hk q e)
  | E8 q =>
    exact Or.inl (PrimitiveSocleExceptionalEOneFactorOrdinaryGenerators.typeE8_genRank_le_ceiling D hk q e)
  | F4 q =>
    exact Or.inl (PrimitiveSocleFFourOneFactorOrdinaryTail.genRank_le_ceiling D hk q e hn)
  | G2 q hs =>
    exact Or.inl (PrimitiveSocleGTwoOneFactorOrdinaryTail.genRank_le_ceiling D hk q hs e hn)
  | twistedA r q hr hs =>
    exact Or.inl (PrimitiveSocleUnitaryOneFactorOrdinaryTail.genRank_le_ceiling D hk r q hr hs e hn)
  | twistedD r q hr =>
    exact Or.inl (PrimitiveSocleTwistedDOneFactorOrdinaryTail.genRank_le_ceiling D hk r hr q e (by omega))
  | twistedE6 q =>
    exact Or.inl (PrimitiveSocleTwistedE6OneFactorOrdinaryGenerators.genRank_le_ceiling D hk q e)
  | trialityD4 q =>
    exact Or.inl (PrimitiveSocleTrialityOneFactorOrdinaryTail.genRank_le_ceiling D hk q e hn)
  | suzuki m hm =>
    exact Or.inl (PrimitiveSocleSuzukiOneFactorOrdinaryTail.genRank_le_ceiling D hk m hm e (by omega))
  | reeG2 m hm =>
    exact Or.inl (PrimitiveSocleReeGTwoOneFactorOrdinaryTail.genRank_le_ceiling D hk m hm e hn)
  | reeF4 m hm =>
    exact Or.inl (PrimitiveSocleReeFFourOneFactorOrdinaryTail.genRank_le_ceiling D hk m (by omega) e hn)
  | tits => exact Or.inr ⟨.tits, trivial, ⟨e⟩⟩
  | sporadic s => exact Or.inr ⟨.sporadic s, trivial, ⟨e⟩⟩

theorem exists_generating_finset_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (hk : D.factorCount = 1)
    (hn : 1024 ≤ Nat.card X) :
    (∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X)) ∨
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model D hCFSG hk hn with h | h
  · obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
    exact Or.inl ⟨U, hgen, hU.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
