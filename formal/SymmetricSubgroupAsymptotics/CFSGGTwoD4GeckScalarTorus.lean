import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom
import Mathlib.Data.Matrix.Cartan

/-! The literal folded G2 torus exponent matrix is unimodular.
Thus every pair of desired nonzero simple-root scalars is realized;
no cube-power or norm surjectivity premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTorus
open CFSGIntegerMatrixPowerHom

def relativeCartan : Matrix (Fin 2) (Fin 2) ℤ := CartanMatrix.G₂.transpose

def inverseExponents : Matrix (Fin 2) (Fin 2) ℤ := !![2,1;3,2]

theorem relativeCartan_right_inverse : relativeCartan*inverseExponents=1 := by decide

theorem relativeCartan_left_inverse : inverseExponents*relativeCartan=1 := by decide

def scalarEquiv (G : Type*) [CommGroup G] : (Fin 2→G)≃*(Fin 2→G) where
  toFun := powerHom relativeCartan
  invFun := powerHom inverseExponents
  left_inv := powerHom_rightInverse inverseExponents relativeCartan relativeCartan_left_inverse
  right_inv := powerHom_rightInverse relativeCartan inverseExponents relativeCartan_right_inverse
  map_mul' := map_mul (powerHom relativeCartan)

theorem scalarEquiv_short {G : Type*} [CommGroup G] (x : Fin 2→G) :
    scalarEquiv G x 0=x 0^2/x 1 := by
  change powerHom relativeCartan x 0=_
  simp only [powerHom_apply,Fin.prod_univ_two]
  change x 0^(2:ℤ)*x 1^(-1:ℤ)=_
  simp only [zpow_ofNat,zpow_neg_one,div_eq_mul_inv]

theorem scalarEquiv_long {G : Type*} [CommGroup G] (x : Fin 2→G) :
    scalarEquiv G x 1=x 1^2/x 0^3 := by
  change powerHom relativeCartan x 1=_
  simp only [powerHom_apply,Fin.prod_univ_two]
  change x 0^(-(3:ℤ))*x 1^(2:ℤ)=_
  simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv,mul_comm]

theorem scalarEquiv_symm_short {G : Type*} [CommGroup G] (x : Fin 2→G) :
    (scalarEquiv G).symm x 0=x 0^2*x 1 := by
  change powerHom inverseExponents x 0=_
  simp only [powerHom_apply,Fin.prod_univ_two]
  change x 0^(2:ℤ)*x 1^(1:ℤ)=_
  simp only [zpow_ofNat,pow_one]

theorem scalarEquiv_symm_long {G : Type*} [CommGroup G] (x : Fin 2→G) :
    (scalarEquiv G).symm x 1=x 0^3*x 1^2 := by
  change powerHom inverseExponents x 1=_
  simp only [powerHom_apply,Fin.prod_univ_two]
  change x 0^(3:ℤ)*x 1^(2:ℤ)=_
  simp only [zpow_ofNat]

theorem powerHom_surjective {G : Type*} [CommGroup G] :
    Function.Surjective (powerHom (G:=G) relativeCartan) := (scalarEquiv G).surjective

theorem range_index_eq_one {G : Type*} [CommGroup G] :
    (powerHom (G:=G) relativeCartan).range.index=1 := by
  rw [MonoidHom.range_eq_top.mpr powerHom_surjective,Subgroup.index_top]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTorus
