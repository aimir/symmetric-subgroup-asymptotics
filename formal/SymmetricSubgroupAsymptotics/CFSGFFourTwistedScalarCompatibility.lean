import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
import Mathlib.Algebra.BigOperators.Fin

/-! The middle simple characters of a twisted F4 torus are paired by
its coefficient endomorphism. This is a commutative-group calculation;
no fixedness or group realization is inferred from it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourTwistedScalarCompatibility
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom

theorem middle_scalar_twist {G : Type*} [CommGroup G] (gamma : G →* G)
    (hgamma : ∀ x,gamma (gamma x)=x^2) (a b : G) :
    powerHom relativeCartan ![a,b,gamma b,gamma a] 2=
      gamma (powerHom relativeCartan ![a,b,gamma b,gamma a] 1) := by
  simp only [powerHom_apply,Fin.prod_univ_four]
  change a^(0:ℤ)*b^(-2:ℤ)*(gamma b)^(2:ℤ)*(gamma a)^(-1:ℤ)=
    gamma (a^(-1:ℤ)*b^(2:ℤ)*(gamma b)^(-1:ℤ)*(gamma a)^(0:ℤ))
  simp only [map_mul,map_inv,map_pow,hgamma,zpow_zero,zpow_neg,zpow_ofNat,
    pow_zero,pow_one,map_one,one_mul,mul_one,inv_pow]
  ac_rfl

end SymmetricSubgroupAsymptotics.CFSGFFourTwistedScalarCompatibility
