import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition

/-! Linear automorphism coordinates for the literal plane-function action.
The affine semidirect product is the same physical wreath coordinate model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFunctionLinearAction
open BinaryPlanePermutationAffineEquiv
variable {R I : Type} [Group R] [MulAction R I]

abbrev Frame := PermutationalWreathProduct Linear R I
abbrev V := I → Plane
abbrev rho0 := PermutationalWreathProduct.functionRepresentation
  (Q := R) (I := I)
  BinaryPlaneCyclicWreathUniform.localRepresentation

def rho : Frame (R := R) (I := I) →*
    (V (I := I) ≃ₗ[ZMod 2] V (I := I)) where
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

end SymmetricSubgroupAsymptotics.BinaryPlaneFunctionLinearAction
