import SymmetricSubgroupAsymptotics.CFSGFiniteFieldPolynomialCurveSpan
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

/-! Translation invariance identifies a cubic-curve pairing from its
initial endpoint. In characteristic three its whole four-coordinate
form factors through the two endpoint coordinates, provided the actual
cubic curve spans the space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCubicTranslationInvariantPairing

open CFSGFiniteFieldPolynomialCurveSpan
variable {K : Type*} [Field K]

def endpointPairing (k : K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] K where
  toFun u :=
    { toFun := fun v => k*(u 0*v 3-u 3*v 0)
      map_add' := by intro v w; change k*(u 0*(v 3+w 3)-u 3*(v 0+w 0)) = _; ring
      map_smul' := by intro a v; change k*(u 0*(a*v 3)-u 3*(a*v 0)) = a*(k*(u 0*v 3-u 3*v 0)); ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change k*((u 0+v 0)*w 3-(u 3+v 3)*w 0) = k*(u 0*w 3-u 3*w 0)+k*(v 0*w 3-v 3*w 0)
    ring
  map_smul' := by
    intro a u
    apply LinearMap.ext
    intro v
    change k*((a*u 0)*v 3-(a*u 3)*v 0) = a*(k*(u 0*v 3-u 3*v 0))
    ring

theorem curve_pairing_eq_cubic_difference
    (B : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] K) (k : K)
    (hbase : ∀ t, B (monomialCurve K 4 0) (monomialCurve K 4 t) = k*t^3)
    (htranslation : ∀ a s t, B (monomialCurve K 4 (a+s)) (monomialCurve K 4 (a+t)) =
      B (monomialCurve K 4 s) (monomialCurve K 4 t)) (s t : K) :
    B (monomialCurve K 4 s) (monomialCurve K 4 t) = k*(t-s)^3 := by
  have he := htranslation (-s) s t
  rw [neg_add_cancel,hbase] at he
  exact he.symm.trans (congrArg (fun z : K => k*z^3) (by ring))

theorem pairing_eq_endpoint [Finite K] [CharP K 3] (hcard : 4 ≤ Nat.card K)
    (B : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] K) (k : K)
    (hbase : ∀ t, B (monomialCurve K 4 0) (monomialCurve K 4 t) = k*t^3)
    (htranslation : ∀ a s t, B (monomialCurve K 4 (a+s)) (monomialCurve K 4 (a+t)) =
      B (monomialCurve K 4 s) (monomialCurve K 4 t)) : B = endpointPairing k := by
  have hspan := monomialCurve_span_eq_top K 4 (by decide) hcard
  apply LinearMap.ext_on_range hspan
  intro s
  apply LinearMap.ext_on_range hspan
  intro t
  rw [curve_pairing_eq_cubic_difference B k hbase htranslation,sub_pow_char]
  change k*(t^3-s^3) = k*((s^0)*(t^3)-(s^3)*(t^0))
  simp only [pow_zero,one_mul,mul_one]

end SymmetricSubgroupAsymptotics.CFSGCubicTranslationInvariantPairing
