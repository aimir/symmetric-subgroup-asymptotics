import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The exact quadratic obstruction in a product of two root operators
sharing a singular axis. Unlike the square of the displacement, this
obstruction survives in characteristic two. No geometry classification
or group-recognition premise is involved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProductQuadratic
open CFSGAlternatingPairOperator CFSGOrthogonalDIndexPairProduct
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem singular_shared_combination (Q : QuadraticForm K V) (u v w : V)
    (hu : Q u = 0) (hv : Q v = 0) (hw : Q w = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (c a b : K) :
    Q (c • u + a • v + b • w) = a * b * Q.polarBilin v w := by
  have hadd (x y : V) : Q (x + y) = Q x + Q y + Q.polarBilin x y :=
    QuadraticMap.map_add Q x y
  rw [hadd, hadd]
  simp only [Q.map_smul, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hu, hv, hw, huv, huw, smul_eq_mul, mul_zero,
    zero_add, add_zero]
  ring

theorem shared_product_displacement_quadratic (Q : QuadraticForm K V) (u v w : V)
    (hu : Q u = 0) (hv : Q v = 0) (hw : Q w = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (a b : K) (x : V) :
    Q ((((LinearMap.id : V →ₗ[K] V) + a • pairOperator Q.polarBilin u v).comp
        ((LinearMap.id : V →ₗ[K] V) + b • pairOperator Q.polarBilin u w) - (LinearMap.id : V →ₗ[K] V)) x) =
      a * b * (Q.polarBilin u x) ^ 2 * Q.polarBilin v w := by
  have huu : Q.polarBilin u u = 0 := by
    change QuadraticMap.polar Q u u = 0
    rw [Q.polar_self, hu, smul_zero]
  have hvu : Q.polarBilin v u = 0 := by
    change QuadraticMap.polar Q v u = 0
    rw [QuadraticMap.polar_comm (Q : V → K) v u]
    exact huv
  rw [pairOperator_shared_product Q.polarBilin u v w huu hvu huw a b]
  have he : (((LinearMap.id : V →ₗ[K] V) + pairOperator Q.polarBilin u (a • v + b • w) -
        (a * b * Q.polarBilin v w) • (Q.polarBilin u).smulRight u - (LinearMap.id : V →ₗ[K] V)) x) =
      (a * Q.polarBilin v x + b * Q.polarBilin w x -
        a * b * Q.polarBilin v w * Q.polarBilin u x) • u +
        (-(Q.polarBilin u x) * a) • v + (-(Q.polarBilin u x) * b) • w := by
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, pairOperator_apply,
      map_add, map_smul, smul_eq_mul]
    module
  rw [he, singular_shared_combination Q u v w hu hv hw huv huw]
  ring

theorem shared_product_singular_forces_orthogonal (Q : QuadraticForm K V) (u v w : V)
    (hu : Q u = 0) (hv : Q v = 0) (hw : Q w = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : V) (hx : Q.polarBilin u x ≠ 0)
    (hs : Q ((((LinearMap.id : V →ₗ[K] V) + a • pairOperator Q.polarBilin u v).comp
        ((LinearMap.id : V →ₗ[K] V) + b • pairOperator Q.polarBilin u w) - (LinearMap.id : V →ₗ[K] V)) x) = 0) :
    Q.polarBilin v w = 0 := by
  rw [shared_product_displacement_quadratic Q u v w hu hv hw huv huw a b x] at hs
  exact (mul_eq_zero.mp hs).resolve_left (mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero _ hx))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProductQuadratic
