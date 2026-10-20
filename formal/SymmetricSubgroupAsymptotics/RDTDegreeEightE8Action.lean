import SymmetricSubgroupAsymptotics.BinaryDegreeEightBaseRoutes
import SymmetricSubgroupAsymptotics.RDTDegreeEightE8Structure

/-! The exceptional registry action is the actual faithful eight-point
Heisenberg action, through its already checked point relabelling. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RDTDegreeEightE8Action

open BinaryDegreeEightBaseRoutes BinaryActionRegistry8

def modelEquiv : BinaryHeisenberg 2 ≃* actions (18 : Fin 26) := by
  let e₀ : BinaryHeisenberg 2 ≃* criticalActionSubgroup .e8 :=
    MonoidHom.ofInjective (BinaryHeisenberg.action_injective 2)
  let e₁ := (criticalActionSubgroup .e8).equivMapOfInjective
    e8PointEquiv.permCongrHom.toMonoidHom e8PointEquiv.permCongrHom.injective
  have h : (criticalActionSubgroup .e8).map e8PointEquiv.permCongrHom.toMonoidHom =
      actions (18 : Fin 26) := base_action_eq .e8
  exact e₀.trans (e₁.trans (MulEquiv.subgroupCongr h))

end SymmetricSubgroupAsymptotics.RDTDegreeEightE8Action

end
