import SymmetricSubgroupAsymptotics.CFSGTwistedA2FieldBasis
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel

/-! Exact rank-two source correspondence. The natural action is faithful
because the ORIGINAL integral tensor space has the explicit eight-vector
basis. The original adjoint group is consequently equivalent to the
actual elementary natural central quotient, without a simplicity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K]

theorem naturalAction_injective : Function.Injective (naturalAction K 2) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply naturalBaseChange_injective K
  have hh := congrArg (fun f : NaturalImage K 2 ≃ₗ[K] NaturalImage K 2 =>
    (f ((baseChange (realizationData 2) K).rangeRestrict x)).val) he
  change (imageRepresentation (realizationData 2) K g
      ((baseChange (realizationData 2) K).rangeRestrict x)).val =
    (imageRepresentation (realizationData 2) K h
      ((baseChange (realizationData 2) K).rangeRestrict x)).val at hh
  simpa only [imageRepresentation_intertwines] using hh

def naturalProjectiveEquiv : Model A K ≃*
    (NaturalElementary K 2 ⧸ Subgroup.center (NaturalElementary K 2)) :=
  (MonoidHom.ofInjective (naturalAction_injective K)).trans
    ((MulEquiv.subgroupCongr (naturalAction_ranges_eq K 2)).trans
      (naturalElementaryProjectiveActionEquiv K 2 (by decide)).symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
