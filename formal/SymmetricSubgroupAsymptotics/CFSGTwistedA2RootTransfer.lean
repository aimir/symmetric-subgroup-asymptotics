import SymmetricSubgroupAsymptotics.CFSGTwistedA2NaturalFaithfulness

/-! An actual homomorphism from natural elementary matrices back to the
original adjoint A2 group. Its construction uses the proven injective
map on the original integral tensor space. Every literal root parameter
is preserved; this transfers matrix WORD identities to source identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix
open CFSGSerreModelRootGeneration
variable (K : Type) [Field K]

def sourceActionRangeEquiv : Model A K ≃* (naturalAction K 2).range :=
  MonoidHom.ofInjective (naturalAction_injective K)

def elementaryActionAsSourceRange : NaturalElementary K 2 →* (naturalAction K 2).range where
  toFun u := ⟨naturalElementaryAction K 2 u, by
    rw [naturalAction_ranges_eq]
    exact ⟨u, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u v)

def elementaryToModel : NaturalElementary K 2 →* Model A K :=
  (sourceActionRangeEquiv K).symm.toMonoidHom.comp (elementaryActionAsSourceRange K)

theorem elementaryToModel_action (u : NaturalElementary K 2) :
    naturalAction K 2 (elementaryToModel K u) = naturalElementaryAction K 2 u := by
  have h := (sourceActionRangeEquiv K).apply_symm_apply (elementaryActionAsSourceRange K u)
  exact congrArg (fun y : (naturalAction K 2).range => y.val) h

theorem elementaryToModel_root (neg : Bool) (i : Fin 2) (t : K) :
    elementaryToModel K (elementaryRoot K (naturalRootUnit K 2) neg i t) =
      modelRoot A K neg i t := by
  apply naturalAction_injective K
  rw [elementaryToModel_action]
  exact (source_root_action_eq_elementary (realizationData 2) K
    (naturalRootUnit K 2) (naturalRootUnit_val K 2) (naturalRootUnit_inv_val K 2)
    neg i t).symm

theorem elementaryToModel_surjective : Function.Surjective (elementaryToModel K) := by
  intro g
  have hg : naturalAction K 2 g ∈ (naturalElementaryAction K 2).range := by
    rw [← naturalAction_ranges_eq]
    exact ⟨g, rfl⟩
  obtain ⟨u, hu⟩ := hg
  refine ⟨u, naturalAction_injective K ?_⟩
  rw [elementaryToModel_action, hu]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
