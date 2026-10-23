import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration

/-! Every element of the ENTIRE fixed natural positive group acts as a
genuine element of the ORIGINAL fixed subgroup on the same integral
image.  The section witnesses and full fixed-U generation are proved,
not supplied as a source-image coverage premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSourceImage
open CFSGTrialityGeckOriginalFixedSections CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckPositiveTwist
open CFSGSerreOrdinaryTwists

theorem fixed_positive_action_mem_source_range (q : CFSG.PrimePower)
    (u : PositiveGroup (q.Extension 3))
    (hu : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u = u) :
    positiveAction (q.Extension 3) u ∈ (fixedImageAction q).range := by
  let R : Subgroup (PositiveGroup (q.Extension 3)) := (fixedImageAction q).range.comap
    (show PositiveGroup (q.Extension 3) →*
      (Image (q.Extension 3) ≃ₗ[q.Extension 3] Image (q.Extension 3)) from
        positiveAction (q.Extension 3))
  have hgen : sectionGenerated (q.Extension 3) (definingFieldAutomorphism q 3) ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨s,t,ht,rfl⟩ | ⟨s,t,ht,rfl⟩)
    · exact longPositiveSection_action_mem_range q s t ht
    · exact shortPositiveSection_action_mem_range q s t
  have hmem : u ∈ sectionGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
    rw [← fixedPositive_eq_sectionGenerated]
    exact hu
  exact hgen hmem

theorem exists_original_fixed_action (q : CFSG.PrimePower)
    (u : PositiveGroup (q.Extension 3))
    (hu : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u = u) :
    ∃ g : CFSGTrialityTripleFixedRoots.Fixed q,
      fixedImageAction q g = positiveAction (q.Extension 3) u :=
  fixed_positive_action_mem_source_range q u hu

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSourceImage
