import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalFieldBasis
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel

/-! The ORIGINAL adjoint A group and its natural elementary projective
image coincide in every characteristic. This correspondence is proved
from the explicit basis of the original integral tensor space; there is
no source simplicity, source kernel or classical-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix
open CFSGSerreModelRootGeneration
variable (K : Type) [Field K] (r : ℕ)

theorem naturalAction_injective : Function.Injective (naturalAction K r) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply naturalBaseChange_injective K r
  have hh := congrArg (fun f : NaturalImage K r ≃ₗ[K] NaturalImage K r =>
    (f ((baseChange (realizationData r) K).rangeRestrict x)).val) he
  change (imageRepresentation (realizationData r) K g
      ((baseChange (realizationData r) K).rangeRestrict x)).val =
    (imageRepresentation (realizationData r) K h
      ((baseChange (realizationData r) K).rangeRestrict x)).val at hh
  simpa only [imageRepresentation_intertwines] using hh

def naturalProjectiveEquiv (hr : 1 ≤ r) : Model (CartanMatrix.A r) K ≃*
    (NaturalElementary K r ⧸ Subgroup.center (NaturalElementary K r)) :=
  (MonoidHom.ofInjective (naturalAction_injective K r)).trans
    ((MulEquiv.subgroupCongr (naturalAction_ranges_eq K r)).trans
      (naturalElementaryProjectiveActionEquiv K r hr).symm)

def sourceActionRangeEquiv : Model (CartanMatrix.A r) K ≃* (naturalAction K r).range :=
  MonoidHom.ofInjective (naturalAction_injective K r)

def elementaryActionAsSourceRange : NaturalElementary K r →* (naturalAction K r).range where
  toFun u := ⟨naturalElementaryAction K r u, by
    rw [naturalAction_ranges_eq]
    exact ⟨u, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u v)

def elementaryToModel : NaturalElementary K r →* Model (CartanMatrix.A r) K :=
  (sourceActionRangeEquiv K r).symm.toMonoidHom.comp (elementaryActionAsSourceRange K r)

theorem elementaryToModel_action (u : NaturalElementary K r) :
    naturalAction K r (elementaryToModel K r u) = naturalElementaryAction K r u := by
  have h := (sourceActionRangeEquiv K r).apply_symm_apply (elementaryActionAsSourceRange K r u)
  exact congrArg (fun y : (naturalAction K r).range => y.val) h

theorem elementaryToModel_root (neg : Bool) (i : Fin r) (t : K) :
    elementaryToModel K r (elementaryRoot K (naturalRootUnit K r) neg i t) =
      modelRoot (CartanMatrix.A r) K neg i t := by
  apply naturalAction_injective K r
  rw [elementaryToModel_action]
  exact (source_root_action_eq_elementary (realizationData r) K
    (naturalRootUnit K r) (naturalRootUnit_val K r) (naturalRootUnit_inv_val K r)
    neg i t).symm

theorem elementaryToModel_surjective : Function.Surjective (elementaryToModel K r) := by
  intro g
  have hg : naturalAction K r g ∈ (naturalElementaryAction K r).range := by
    rw [← naturalAction_ranges_eq]
    exact ⟨g, rfl⟩
  obtain ⟨u, hu⟩ := hg
  refine ⟨u, naturalAction_injective K r ?_⟩
  rw [elementaryToModel_action, hu]

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
