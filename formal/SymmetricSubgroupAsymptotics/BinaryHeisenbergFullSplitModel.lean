import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.LinearSemidirectProperNormalFPacket
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The full natural Heisenberg extension is a displayed semidirect product,
with the original action and central involution. No group table is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
open BinaryHeisenbergEightNaturalHeads

def action : H →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    rho.asGroupHom

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model action

theorem action_apply (g : H) (v : V) : action g v = rho g v := rfl

theorem z_central : generators 0 ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨i, rfl⟩ := BinaryEightOriginalRowActions.heisenbergRow_bijective.2 g
  have hc : ∀ i : Fin 32, BinaryHeisenbergTopCentralCore.PointEq
      (BinaryEightOriginalRowActions.heisenbergRow i * generators 0)
      (generators 0 * BinaryEightOriginalRowActions.heisenbergRow i) := by
    decide +kernel
  exact BinaryHeisenbergTopCentralCore.eq_of_pointEq (hc i)

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
