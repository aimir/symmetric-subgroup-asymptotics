import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Three genuine rays of a pencil determine its linear representative.
The codomain may be larger than the domain: no ambient surjectivity or
projective recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGLinearThreeRayPencil
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem exists_scalar_of_three_pencil_rays (e L : V →ₗ[K] W) (x y : V)
    (hxy : LinearIndependent K ![e x,e y]) (t t' : K) (htt : t ≠ t')
    (hy : L y ∈ K ∙ e y)
    (ht : L (x + t • y) ∈ K ∙ e (x + t • y))
    (ht' : L (x + t' • y) ∈ K ∙ e (x + t' • y)) :
    ∃ a : K, L x = a • e x ∧ L y = a • e y := by
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp ht'
  have hLc : L (x + t • y) = c • (e x + t • e y) := by
    rw [map_add, map_smul] at hc
    exact hc.symm
  have hLd : L (x + t' • y) = d • (e x + t' • e y) := by
    rw [map_add, map_smul] at hd
    exact hd.symm
  have hdiff : (t' - t) • L y = d • (e x + t' • e y) - c • (e x + t • e y) := by
    calc
      _ = L (x + t' • y) - L (x + t • y) := by rw [map_add, map_add, map_smul, map_smul]; module
      _ = _ := by rw [hLc, hLd]
  have hz : (d - c) • e x + (d * t' - c * t - (t' - t) * b) • e y = 0 := by
    calc
      _ = (d • (e x + t' • e y) - c • (e x + t • e y)) - (t' - t) • (b • e y) := by module
      _ = 0 := by rw [← hdiff, hb]; exact sub_self _
  obtain ⟨hdc, hcoeff⟩ := LinearIndependent.pair_iff.mp hxy (d - c)
    (d * t' - c * t - (t' - t) * b) hz
  have hdc' : d = c := sub_eq_zero.mp hdc
  have hprod : (t' - t) * (c - b) = 0 := by
    calc
      _ = c * t' - c * t - (t' - t) * b := by ring
      _ = 0 := by simpa only [hdc'] using hcoeff
  have hcb : c = b := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left
    (sub_ne_zero.mpr (Ne.symm htt)))
  refine ⟨c, ?_, by rw [hcb]; exact hb.symm⟩
  apply sub_eq_zero.mp
  calc
    L x - c • e x = (L (x + t • y) - c • (e x + t • e y)) := by
      rw [map_add, map_smul, ← hb, ← hcb]
      module
    _ = 0 := sub_eq_zero.mpr hLc

end SymmetricSubgroupAsymptotics.CFSGLinearThreeRayPencil
