import SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Actual quadratic zero, including characteristic two, is retained
by scalar extension of a subspace over the quadratic fixed field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (sigma : K ≃+* K) (theta : K) (htheta : sigma theta ≠ theta) (F : Subfield K)

include sigma theta htheta in
theorem quadratic_zero_span_iff (hsigma : ∀ a, sigma (sigma a) = a)
    (hF : ∀ a, a ∈ F ↔ sigma a = a) (Q : QuadraticForm K V) (S : Submodule F V) :
    (∀ z ∈ Submodule.span K (S : Set V), Q z = 0) ↔ ∀ z ∈ S, Q z = 0 := by
  constructor
  · exact fun h z hz => h z (Submodule.subset_span hz)
  · intro h z hz
    obtain ⟨x, hx, y, hy, he⟩ := exists_span_decomposition sigma theta htheta F hsigma hF S z hz
    have hp : QuadraticMap.polar Q x y = 0 := by
      change Q (x + y) - Q x - Q y = 0
      rw [h (x + y) (S.add_mem hx hy), h x hx, h y hy]
      ring
    rw [he, QuadraticMap.map_add Q x (theta • y), Q.map_smul, QuadraticMap.polar_smul_right,
      h x hx, h y hy, hp, smul_zero, smul_zero, add_zero, zero_add]

end SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
