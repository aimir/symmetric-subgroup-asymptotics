import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortDerivedImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration

/-! The entire fixed natural positive group acts through the DERIVED
original triality fixed subgroup, uniformly for every prime power. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveDerivedImage
open CFSGTrialityGeckShortDerivedImage CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckPositiveTwist CFSGSerreOrdinaryTwists

theorem fixed_positive_action_mem_derived_range (q : CFSG.PrimePower)
    (u : PositiveGroup (q.Extension 3))
    (hu : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u = u) :
    positiveAction (q.Extension 3) u ∈ (derivedImageAction q).range := by
  let R : Subgroup (PositiveGroup (q.Extension 3)) := (derivedImageAction q).range.comap
    (show PositiveGroup (q.Extension 3) →*
      (Image (q.Extension 3) ≃ₗ[q.Extension 3] Image (q.Extension 3)) from
        positiveAction (q.Extension 3))
  have hgen : sectionGenerated (q.Extension 3) (definingFieldAutomorphism q 3) ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨s,t,ht,rfl⟩ | ⟨s,t,ht,rfl⟩)
    · exact long_positive_action_mem_derived q s t ht
    · exact short_positive_action_mem_derived q s t
  have hmem : u ∈ sectionGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
    rw [← fixedPositive_eq_sectionGenerated]
    exact hu
  exact hgen hmem

theorem exists_original_derived_action (q : CFSG.PrimePower)
    (u : PositiveGroup (q.Extension 3))
    (hu : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u = u) :
    ∃ g : commutator (CFSGTrialityTripleFixedRoots.Fixed q),
      derivedImageAction q g = positiveAction (q.Extension 3) u :=
  fixed_positive_action_mem_derived_range q u hu

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveDerivedImage
