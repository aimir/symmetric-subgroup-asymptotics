import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.CFSGSporadicGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration

/-!
# The exact remaining concrete cases for simple two-generation

The alternating family and twenty sporadic constructions are proved directly.
The residual predicate contains precisely the Lie-type branches and the six
sporadic constructions not covered by those direct proofs. The assembly below
preserves the exact public finite-simple two-generation conclusion. It does not
assert that its remaining model cases have already been proved.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

/-- The exact branches not discharged by the elementary constructions. -/
def RemainingGenerationIndex : CFSG.Index → Prop
  | .cyclic _ _ => False
  | .alternating _ _ => False
  | .sporadic s => SporadicGenerationResidual s
  | _ => True

theorem noncommutative_of_simple_centerless (G : Type*) [Group G]
    [IsSimpleGroup G] (hc : IsCenterless G) : ¬ IsMulCommutative G := by
  intro hcomm
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (hc g (fun h => (isMulCommutative_iff.mp hcomm) g h))

/-- This dispatch uses actual generating subsets, without order matches or
an unproved identification between the CFSG models and other group models. -/
theorem model_twoGenerated_or_remaining (i : CFSG.Index) :
    ¬ IsMulCommutative i.Model → TwoGenerated i.Model ∨ RemainingGenerationIndex i := by
  cases i <;> try exact fun _ => Or.inr trivial
  case cyclic p hp =>
    intro hn
    exfalso
    apply hn
    change IsMulCommutative (Multiplicative (ZMod p))
    infer_instance
  case alternating n hn =>
    intro _
    left
    obtain ⟨a, ha⟩ := CFSGAlternatingGeneration.exists_generating_tuple n hn
    exact of_generating_family a ha (by simp)
  case sporadic s =>
    intro _
    exact sporadic_twoGenerated_or_residual s

/-- Exact reduction to the still-open concrete cases. This theorem is not
advertised as a CFSG-only proof until `remaining` has been supplied by proofs. -/
theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model → RemainingGenerationIndex i → TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G →
      TwoGenerated G := by
  intro G _ _ hsimple hc
  letI := hsimple
  let W := simpleModelWitness hCFSG G
  letI := W.finite_model
  letI := W.simple_model
  have hm : IsCenterless W.index.Model := (isCenterless_congr W.equiv).mp hc
  have hgen : TwoGenerated W.index.Model := by
    rcases model_twoGenerated_or_remaining W.index
      (noncommutative_of_simple_centerless W.index.Model hm) with h | h
    · exact h
    · exact remaining W.index hm h
  exact of_mulEquiv W.equiv.symm hgen

end SymmetricSubgroupAsymptotics.CFSGReduction
