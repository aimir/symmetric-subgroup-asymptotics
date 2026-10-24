import SymmetricSubgroupAsymptotics.CFSGFiniteFieldPolynomialCurveSpan
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

/-! The actual linear translation of the cubic evaluation curve. Agreement
on that curve determines a linear action when the field has at least four
elements. Its endpoint action in characteristic three is a shear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCubicCurveTranslationLinear
open CFSGFiniteFieldPolynomialCurveSpan
variable {K : Type*} [Field K]

def translation (a : K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun u := ![u 0, a*u 0+u 1, a^2*u 0+2*a*u 1+u 2,
    a^3*u 0+3*a^2*u 1+3*a*u 2+u 3]
  map_add' := by
    intro u v
    funext i
    fin_cases i
    · change u 0+v 0 = u 0+v 0
      rfl
    · change a*(u 0+v 0)+(u 1+v 1) = (a*u 0+u 1)+(a*v 0+v 1)
      ring
    · change a^2*(u 0+v 0)+2*a*(u 1+v 1)+(u 2+v 2) =
        (a^2*u 0+2*a*u 1+u 2)+(a^2*v 0+2*a*v 1+v 2)
      ring
    · change a^3*(u 0+v 0)+3*a^2*(u 1+v 1)+3*a*(u 2+v 2)+(u 3+v 3) =
        (a^3*u 0+3*a^2*u 1+3*a*u 2+u 3)+(a^3*v 0+3*a^2*v 1+3*a*v 2+v 3)
      ring
  map_smul' := by
    intro c u
    funext i
    fin_cases i
    · change c*u 0 = c*u 0
      rfl
    · change a*(c*u 0)+c*u 1 = c*(a*u 0+u 1)
      ring
    · change a^2*(c*u 0)+2*a*(c*u 1)+c*u 2 = c*(a^2*u 0+2*a*u 1+u 2)
      ring
    · change a^3*(c*u 0)+3*a^2*(c*u 1)+3*a*(c*u 2)+c*u 3 =
        c*(a^3*u 0+3*a^2*u 1+3*a*u 2+u 3)
      ring

theorem translation_curve (a t : K) :
    translation a (monomialCurve K 4 t) = monomialCurve K 4 (a+t) := by
  funext i
  fin_cases i
  · change t^0 = (a+t)^0
    simp only [pow_zero]
  · change a*t^0+t^1 = (a+t)^1
    ring
  · change a^2*t^0+2*a*t^1+t^2 = (a+t)^2
    ring
  · change a^3*t^0+3*a^2*t^1+3*a*t^2+t^3 = (a+t)^3
    ring

theorem translation_first (a : K) (u : Fin 4 → K) : translation a u 0 = u 0 := rfl

theorem translation_last [CharP K 3] (a : K) (u : Fin 4 → K) :
    translation a u 3 = a^3*u 0+u 3 := by
  change a^3*u 0+3*a^2*u 1+3*a*u 2+u 3 = _
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [hthree]
  ring

theorem map_eq_of_curve_translation [Finite K] (hcard : 4 ≤ Nat.card K)
    {M : Type*} [AddCommGroup M] [Module K M]
    (f e : (Fin 4 → K) →ₗ[K] M) (a : K)
    (h : ∀ t, f (monomialCurve K 4 t) = e (monomialCurve K 4 (a+t))) :
    f = e.comp (translation a) := by
  apply LinearMap.ext_on_range (monomialCurve_span_eq_top K 4 (by decide) hcard)
  intro t
  exact (h t).trans (congrArg e (translation_curve a t).symm)

end SymmetricSubgroupAsymptotics.CFSGCubicCurveTranslationLinear
