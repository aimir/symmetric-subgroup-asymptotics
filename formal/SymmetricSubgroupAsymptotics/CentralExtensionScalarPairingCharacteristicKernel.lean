import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCentre

/-! The actual scalar commutator identifies the quotient kernel with the
intrinsic centre. Its invariance under every automorphism is derived
from the existing centre theorem, without a new quotient-action premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCharacteristicKernel
open CentralExtensionScalarPairingIndex CentralExtensionScalarPairingCentre
variable {F V N : Type*} [Field F] [AddCommGroup V] [Module F V] [Group N]
    (D : Data (F := F) (V := V) (N := N))

theorem projection_ker_eq_center : D.projection.ker=Subgroup.center N :=
  D.central_range.symm.trans (center_eq_central_range D).symm

theorem projection_ker_characteristic : D.projection.ker.Characteristic := by
  rw [projection_ker_eq_center D]
  infer_instance

theorem projection_ker_map_eq (f : MulAut N) :
    D.projection.ker.map f.toMonoidHom=D.projection.ker :=
  Subgroup.characteristic_iff_map_eq.mp (projection_ker_characteristic D) f

end SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCharacteristicKernel
