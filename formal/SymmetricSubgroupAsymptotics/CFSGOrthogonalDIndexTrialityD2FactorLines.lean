import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RankOne
import Mathlib.LinearAlgebra.Span.Basic

/-! Zero determinant of two nonzero residual factors identifies their
actual one-dimensional submodule. No projective label is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem vectorDet_zero_iff_proportional (u v : Fin 2 → K) (hu : u ≠ 0) :
    vectorDet K u v = 0 ↔ ∃ a : K, v = a • u := by
  constructor
  · intro hdet
    by_cases hu0 : u 0 = 0
    · have hu1 : u 1 ≠ 0 := by
        intro hz
        apply hu
        funext i
        fin_cases i <;> simp [hu0, hz]
      have hm : u 1 * v 0 = 0 := by
        simpa only [vectorDet, hu0, zero_mul, zero_sub, neg_eq_zero] using hdet
      have hv0 : v 0 = 0 := (mul_eq_zero.mp hm).resolve_left hu1
      refine ⟨v 1 / u 1, ?_⟩
      funext i
      fin_cases i <;> simp [hu0, hv0, div_mul_cancel₀ _ hu1]
    · have hh : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp hdet
      refine ⟨v 0 / u 0, ?_⟩
      funext i
      fin_cases i
      · change v 0 = (v 0 / u 0) * u 0
        exact (div_mul_cancel₀ _ hu0).symm
      · change v 1 = (v 0 / u 0) * u 1
        calc
          v 1 = (u 0 * v 1) / u 0 := by field_simp [hu0] <;> ring
          _ = (u 1 * v 0) / u 0 := congrArg (fun x => x / u 0) hh
          _ = (v 0 / u 0) * u 1 := by ring
  · rintro ⟨a, rfl⟩
    simp only [vectorDet, Pi.smul_apply, smul_eq_mul]
    ring

theorem factor_line_eq_of_vectorDet_zero (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : vectorDet K u v = 0) : Submodule.span K {u} = Submodule.span K {v} := by
  obtain ⟨a, ha⟩ := (vectorDet_zero_iff_proportional K u v hu).mp hd
  have ha0 : a ≠ 0 := by
    intro hz
    exact hv (by simpa only [hz, zero_smul] using ha)
  apply Submodule.span_singleton_eq_span_singleton.mpr
  exact ⟨Units.mk0 a ha0, ha.symm⟩

theorem pairwise_factor_line_alternative (u p v q : Fin 2 → K)
    (hu : u ≠ 0) (hp : p ≠ 0) (hv : v ≠ 0) (hq : q ≠ 0)
    (hd : Matrix.det (columnMap K u p + columnMap K v q) = 0) :
    Submodule.span K {u} = Submodule.span K {v} ∨
      Submodule.span K {p} = Submodule.span K {q} := by
  rw [outer_sum_determinant] at hd
  rcases mul_eq_zero.mp hd with hc | hr
  · exact Or.inl (factor_line_eq_of_vectorDet_zero K u v hu hv hc)
  · exact Or.inr (factor_line_eq_of_vectorDet_zero K p q hp hq hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
