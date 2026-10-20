import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition

/-! Linear automorphism coordinates for the literal plane-function action.
The affine semidirect product is the same physical wreath coordinate model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearAction
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)

abbrev V := Fin 4 → Plane
abbrev rho0 := PermutationalWreathProduct.functionRepresentation
  (Q := Equiv.Perm (Fin 4)) (I := Fin 4)
  BinaryPlaneCyclicWreathUniform.localRepresentation

def rho : Frame →* (V ≃ₗ[ZMod 2] V) where
  toFun w :=
    { toLinearMap := rho0 w
      invFun := rho0 w⁻¹
      left_inv v := by
        change (rho0 w⁻¹ * rho0 w) v=v
        rw [←map_mul,inv_mul_cancel,map_one]
        rfl
      right_inv v := by
        change (rho0 w * rho0 w⁻¹) v=v
        rw [←map_mul,mul_inv_cancel,map_one]
        rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun rho0.map_one v
  map_mul' w z := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (rho0.map_mul w z) v

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearAction
