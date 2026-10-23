import SymmetricSubgroupAsymptotics.CFSGFFourE6SignedFixedInclusion
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRangePreimage

/-! The literal folded F4 matrix group is exactly the group generated
by the two actual identity-diagram-fixed E6 unipotent groups. This is a
subgroup equality on the original matrix carrier, not recognition of a
named abstract group or faithfulness of its restricted action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
open CFSGFFourSerreMatrices CFSGFFourE6SignedFixedInclusion
open CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreQuadraticMatrix

theorem folded_root_eq_orbitParameter (K : Type) [Field K]
    (neg : Bool) (a : Fin 4) (t : K) :
    canonicalRoot realizationData K neg a t = orbitParameter K neg a t := by
  cases neg
  · exact folded_positive_root K a t
  · exact folded_negative_root K a t

theorem fixedRootGenerated_le_folded (K : Type) [Field K] [Finite K] :
    fixedRootGenerated K (RingEquiv.refl K) ≤ canonicalElementaryGroup realizationData K := by
  apply sup_le
  · intro u hu
    exact signedFixed_mem_folded K false ⟨u, hu⟩
  · intro u hu
    exact signedFixed_mem_folded K true ⟨u, hu⟩

theorem fixedRootGenerated_eq_folded (K : Type) [Field K] [Finite K] :
    fixedRootGenerated K (RingEquiv.refl K) = canonicalElementaryGroup realizationData K := by
  apply le_antisymm (fixedRootGenerated_le_folded K)
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, a, t, rfl⟩
  rw [folded_root_eq_orbitParameter]
  exact orbitParameter_mem_generated K (RingEquiv.refl K) neg a t rfl

theorem folded_le_fixedRangePreimage (K : Type) [Field K] [Finite K] :
    canonicalElementaryGroup realizationData K ≤ ambientFixedRangePreimage K (RingEquiv.refl K) := by
  rw [← fixedRootGenerated_eq_folded K]
  exact fixedRootGenerated_le_preimage K (RingEquiv.refl K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
