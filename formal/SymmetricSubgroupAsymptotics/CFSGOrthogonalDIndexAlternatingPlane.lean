import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A nonzero alternating pairing splits off an actual nondegenerate
two-dimensional plane, in every characteristic. This is the elementary
linear-algebra step for a characteristic-two component argument; no
Dickson invariant or parity classification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingPlane
open LinearMap
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def planeMap (u v : V) : K × K →ₗ[K] V where
  toFun a := a.1 • u + a.2 • v
  map_add' a b := by
    change (a.1 + b.1) • u + (a.2 + b.2) • v =
      (a.1 • u + a.2 • v) + (b.1 • u + b.2 • v)
    rw [add_smul, add_smul]
    abel
  map_smul' c a := by
    change (c * a.1) • u + (c * a.2) • v = c • (a.1 • u + a.2 • v)
    simp only [smul_add, smul_smul]

theorem plane_coefficients_zero (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v ≠ 0) (a b : K)
    (hz : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have hvu : B v u ≠ 0 := fun h => huv (hB.isRefl v u h)
  have hu := congrArg (fun x => B u x) hz
  have hv := congrArg (fun x => B v x) hz
  dsimp only at hu hv
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right,
    hB.self_eq_zero u, mul_zero, zero_add, LinearMap.BilinForm.zero_right] at hu
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right,
    hB.self_eq_zero v, mul_zero, add_zero, LinearMap.BilinForm.zero_right] at hv
  exact ⟨(mul_eq_zero.mp hv).resolve_right hvu, (mul_eq_zero.mp hu).resolve_right huv⟩

theorem planeMap_injective (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v ≠ 0) : Function.Injective (planeMap (K := K) u v) := by
  intro a b hab
  have hz : planeMap (K := K) u v (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hc := plane_coefficients_zero B hB u v huv (a.1 - b.1) (a.2 - b.2) hz
  exact Prod.ext (sub_eq_zero.mp hc.1) (sub_eq_zero.mp hc.2)

theorem plane_range_finrank (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v ≠ 0) :
    Module.finrank K (planeMap (K := K) u v).range = 2 := by
  have he := (LinearEquiv.ofInjective (planeMap (K := K) u v)
    (planeMap_injective B hB u v huv)).finrank_eq
  simpa using he.symm

theorem plane_restrict_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v ≠ 0) :
    (B.restrict (planeMap (K := K) u v).range).Nondegenerate := by
  let P := (planeMap (K := K) u v).range
  have huP : u ∈ P := ⟨(1, 0), by simp [planeMap]⟩
  have hvP : v ∈ P := ⟨(0, 1), by simp [planeMap]⟩
  have hvu : B v u ≠ 0 := fun h => huv (hB.isRefl v u h)
  have hsep : ∀ x : P, (∀ y : P, (B.restrict P) x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := x.property
    have heU := hx ⟨u, huP⟩
    have heV := hx ⟨v, hvP⟩
    change B x.val u = 0 at heU
    change B x.val v = 0 at heV
    rw [← ha] at heU heV
    change B (a.1 • u + a.2 • v) u = 0 at heU
    change B (a.1 • u + a.2 • v) v = 0 at heV
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
      hB.self_eq_zero u, mul_zero, zero_add] at heU
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
      hB.self_eq_zero v, mul_zero, add_zero] at heV
    have ha0 : a.1 = 0 := (mul_eq_zero.mp heV).resolve_right huv
    have ha1 : a.2 = 0 := (mul_eq_zero.mp heU).resolve_right hvu
    apply Subtype.ext
    change x.val = 0
    rw [← ha]
    change a.1 • u + a.2 • v = 0
    rw [ha0, ha1, zero_smul, zero_smul, add_zero]
  refine ⟨hsep, fun x hx => hsep x (fun y => ?_)⟩
  exact hB.isRefl y.val x.val (hx y)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingPlane
