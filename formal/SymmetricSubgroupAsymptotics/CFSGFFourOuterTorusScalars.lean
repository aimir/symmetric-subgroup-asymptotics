import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
import Mathlib.Algebra.BigOperators.Fin

/-! A two-coordinate specialization of the literal F4 Cartan power map.
This identity is valid in every commutative group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOuterTorusScalars
open CFSGIntegerMatrixPowerHom CFSGFFourRelativeScalarIndex

theorem outer_torus_scalars {G : Type*} [CommGroup G] (a u : G) :
    powerHom relativeCartan ![a,1,1,u]=![a^2,a⁻¹,u⁻¹,u^2] := by
  funext i
  rw [powerHom_apply,Fin.prod_univ_four]
  fin_cases i
  · change a^(2:ℤ)*1^(-1:ℤ)*1^(0:ℤ)*u^(0:ℤ)=a^2
    simp [zpow_ofNat]
  · change a^(-1:ℤ)*1^(2:ℤ)*1^(-1:ℤ)*u^(0:ℤ)=a⁻¹
    simp
  · change a^(0:ℤ)*1^(-2:ℤ)*1^(2:ℤ)*u^(-1:ℤ)=u⁻¹
    simp
  · change a^(0:ℤ)*1^(0:ℤ)*1^(-1:ℤ)*u^(2:ℤ)=u^2
    simp [zpow_ofNat]

end SymmetricSubgroupAsymptotics.CFSGFFourOuterTorusScalars
