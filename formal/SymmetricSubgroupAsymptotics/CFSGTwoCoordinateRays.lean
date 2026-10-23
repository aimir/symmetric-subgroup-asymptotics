import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-! The exact two-coordinate wedge criterion for distinct projective
rays. The scalar witness is constructed by a nonzero coordinate pivot,
without an arbitrary determinant or basis-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwoCoordinateRays
variable {K : Type*} [Field K]

theorem exists_smul_of_wedge_zero (v w : Fin 2 → K) (hw : w ≠ 0)
    (hdet : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : K, v = c • w := by
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hz
      apply hw
      ext i
      fin_cases i <;> assumption
    have hv0 : v 0 = 0 := by
      have hh : v 0 * w 1 = 0 := by simpa only [hw0, mul_zero, sub_zero] using hdet
      exact (mul_eq_zero.mp hh).resolve_right hw1
    refine ⟨v 1 / w 1, ?_⟩
    ext i
    fin_cases i
    · change v 0 = (v 1 / w 1) * w 0
      rw [hv0, hw0, mul_zero]
    · change v 1 = (v 1 / w 1) * w 1
      exact (div_mul_cancel₀ (v 1) hw1).symm
  · refine ⟨v 0 / w 0, ?_⟩
    ext i
    fin_cases i
    · change v 0 = (v 0 / w 0) * w 0
      exact (div_mul_cancel₀ (v 0) hw0).symm
    · change v 1 = (v 0 / w 0) * w 1
      rw [div_mul_eq_mul_div₀]
      exact (eq_div_iff hw0).mpr (sub_eq_zero.mp hdet).symm

theorem wedge_ne_zero_of_distinct_rays (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : (K ∙ v : Submodule K (Fin 2 → K)) ≠ K ∙ w) :
    v 0 * w 1 - v 1 * w 0 ≠ 0 := by
  intro hdet
  obtain ⟨c, hc⟩ := exists_smul_of_wedge_zero v w hw hdet
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv
    simpa only [hz, zero_smul] using hc
  apply hne
  rw [hc]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) w

end SymmetricSubgroupAsymptotics.CFSGTwoCoordinateRays
