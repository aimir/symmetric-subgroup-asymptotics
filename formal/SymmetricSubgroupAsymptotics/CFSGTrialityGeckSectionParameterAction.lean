import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership

/-! Exact parameter action on the literal conjugated root words used
for fixed-height sections. No scalar-sign choice or root-space action
is supplied as an assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterAction
open CFSGSerreDiagram CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityD4PositiveRootOrbits

theorem outer_triality (k : Fin 3) :
    trialityPermutation (CFSGTrialityFixedWeylWords.outerNode k) =
      CFSGTrialityFixedWeylWords.outerNode (cycle k) := by
  fin_cases k <;> decide

theorem shortFactor_action (K : Type) [CommRing K] (σ : K ≃+* K)
    (s k : Fin 3) (t : K) :
    unitTwist K σ (shortFactor K s k t) = shortFactor K s (cycle k) (σ t) := by
  simp only [shortFactor, map_mul, map_inv, shortTransport_fixed,
    unitTwist_raw_root, outer_triality]

theorem longSection_action (K : Type) [CommRing K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) :
    unitTwist K σ (longSection K s neg t) = longSection K s neg (σ t) := by
  simp only [longSection, map_mul, map_inv, longTransport_fixed, unitTwist_raw_root] <;> rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterAction
