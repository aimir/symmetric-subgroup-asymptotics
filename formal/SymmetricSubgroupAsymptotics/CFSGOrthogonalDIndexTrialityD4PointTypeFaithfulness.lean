import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeOrthogonality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneActionFaithful

/-! Incidence recovers each original plane from its singular points.
Consequently the constructed point action of the actual index-three
subgroup is faithful whenever the original projective model is simple. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem pointTypeAction_injective [IsSimpleGroup (elementaryProjective K 4)] :
    Function.Injective (pointTypeAction K p) := by
  intro f g h
  apply Subtype.ext
  apply singularActionHom_injective K p 0
  apply Equiv.ext
  intro P
  have he : (⟨(singularActionHom K p 0 f.val P).val,
      (singularActionHom K p 0 f.val P).property.2⟩ : Subspaces (splitQuadraticForm K 4)) =
      ⟨(singularActionHom K p 0 g.val P).val,
      (singularActionHom K p 0 g.val P).property.2⟩ := by
    apply subspace_ext
    intro U
    obtain ⟨V, rfl⟩ := (pointTypeAction K p f).surjective U
    rw [pointTypeAction_incidence K p f V P]
    have hh : pointTypeAction K p f V = pointTypeAction K p g V :=
      congrArg (fun a : Equiv.Perm (OriginalPoints K) => a V) h
    rw [hh, pointTypeAction_incidence K p g V P]
  have hv := congrArg (fun T : Subspaces (splitQuadraticForm K 4) => T.val) he
  exact Subtype.ext hv

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
