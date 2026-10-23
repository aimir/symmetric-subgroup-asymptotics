import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots

/-! The independently defined natural relative-root subgroup maps into
the SAME original Derived action preimage, generator by generator. This
is the useful direction for frame elimination; its converse remains a
separate generation theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedRelativeGroup
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDPairedRootImages CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDDerivedNegativePairedRoots CFSGSerreOrdinaryTwists

theorem pairedRoot_eq_natural (s : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (a : q.Extension 2) :
    pairedRoot (s + 2) q neg a = (pairedNaturalRoot s q neg a).val := by
  change rootTransvection (q.Extension 2) (s + 4) neg
      (CFSGOrthogonalDGenerationForkTorus.pen (s + 2)) a *
      rootTransvection (q.Extension 2) (s + 4) neg
        (CFSGOrthogonalDGenerationForkTorus.last (s + 2))
        (definingFieldAutomorphism q 2 a) = _
  rw [definingFieldAutomorphism_apply]
  rfl

theorem relativeRootGroup_le_derived_unit_image (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup (s + 2) q ≤
      (naturalDerivedPreimage s q).map (elementaryRootGroup (q.Extension 2) (s + 4)).subtype := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨neg, i, a, rfl⟩ | ⟨neg, a, rfl⟩
  · refine ⟨naturalRoot s q neg (CFSGTwistedDSingularPrefix.chainNode (s + 2) i)
      (a : q.Extension 2), ?_, rfl⟩
    exact CFSGTwistedDDerivedChainParameters.parameter_mem_derived_preimage
      s q neg i (a : q.Extension 2) a.property
  · refine ⟨pairedNaturalRoot s q neg a, ?_, (pairedRoot_eq_natural s q neg a).symm⟩
    cases neg
    · exact paired_mem_derived_preimage s q a
    · exact paired_negative_mem_derived_preimage s q a

end SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedRelativeGroup
