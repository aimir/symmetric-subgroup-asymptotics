import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! A genuinely nontrivial field involution separates the commutant of
paired square-zero words. Products of their actual displacements first
recover the quadratic term; two field coefficients then separate both
linear directions. No interpolation by the base-field cardinal is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPairedSquareZeroCommutant
variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

def displacement (E F : B) (σ : K ≃+* K) (a : K) : B :=
  a • E + σ a • F + (a * σ a) • (E * F)

theorem displacement_product (E F : B) (hE : E * E = 0) (hF : F * F = 0)
    (hEF : E * F = F * E) (σ : K ≃+* K) (a b : K) :
    displacement E F σ a * displacement E F σ b =
      (a * σ b + σ a * b) • (E * F) := by
  have h1 : E * (E * F) = 0 := by rw [← mul_assoc, hE, zero_mul]
  have h2 : F * (E * F) = 0 := by rw [← mul_assoc, ← hEF, mul_assoc, hF, mul_zero]
  have h3 : (E * F) * E = 0 := by rw [mul_assoc, ← hEF, ← mul_assoc, hE, zero_mul]
  have h4 : (E * F) * F = 0 := by rw [mul_assoc, hF, mul_zero]
  have h5 : (E * F) * (E * F) = 0 := by rw [← mul_assoc, h3, zero_mul]
  simp only [displacement, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, hE, hF, ← hEF, h1, h2, h3, h4, h5, smul_zero, add_zero, zero_add,
    add_smul]
  rw [mul_comm b (σ a), mul_comm (σ b) a]
  exact add_comm _ _

theorem commute_of_paired_words (E F A : B)
    (hE : E * E = 0) (hF : F * F = 0) (hEF : E * F = F * E)
    (σ : K ≃+* K) (θ : K) (hθ : σ θ ≠ θ)
    (htrace : ∃ a b : K, a * σ b + σ a * b ≠ 0)
    (hA : ∀ a : K, A * ((1 + a • E) * (1 + σ a • F)) =
      ((1 + a • E) * (1 + σ a • F)) * A) :
    A * E = E * A ∧ A * F = F * A := by
  let S : Submodule K B :=
    { carrier := {x | A * x = x * A}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change A * x = x * A at hx
        change A * y = y * A at hy
        change A * (x + y) = (x + y) * A
        rw [mul_add, add_mul, hx, hy]
      smul_mem' := by
        intro a x hx
        change A * x = x * A at hx
        change A * (a • x) = (a • x) * A
        rw [mul_smul_comm, smul_mul_assoc, hx] }
  have hN (a : K) : displacement E F σ a ∈ S := by
    have heq : (1 + a • E) * (1 + σ a • F) = 1 + displacement E F σ a := by
      simp only [displacement, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, smul_add, smul_smul, mul_comm (σ a) a]
      abel
    have h := hA a
    rw [heq] at h
    simp only [mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  obtain ⟨a, b, hab⟩ := htrace
  have hprod : displacement E F σ a * displacement E F σ b ∈ S := by
    change A * (_ * _) = (_ * _) * A
    rw [← mul_assoc, hN a, mul_assoc, hN b, ← mul_assoc]
  rw [displacement_product E F hE hF hEF] at hprod
  have hquad : E * F ∈ S := by
    have h := S.smul_mem (a * σ b + σ a * b)⁻¹ hprod
    simpa only [smul_smul, inv_mul_cancel₀ hab, one_smul] using h
  have hlinear (c : K) : c • E + σ c • F ∈ S := by
    have h := S.sub_mem (hN c) (S.smul_mem (c * σ c) hquad)
    simpa only [displacement, add_sub_cancel_right] using h
  have hone : E + F ∈ S := by simpa only [map_one, one_smul] using hlinear 1
  have hd : (σ θ - θ) • F ∈ S := by
    have h := S.sub_mem (hlinear θ) (S.smul_mem θ hone)
    convert h using 1 <;> module
  have hF' : F ∈ S := by
    have h := S.smul_mem (σ θ - θ)⁻¹ hd
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hθ), one_smul] using h
  have hE' : E ∈ S := by
    have h := S.sub_mem hone hF'
    simpa only [add_sub_cancel_right] using h
  exact ⟨hE', hF'⟩

theorem trace_pair_exists (σ : K ≃+* K) (θ : K) (hθ : σ θ ≠ θ) :
    ∃ a b : K, a * σ b + σ a * b ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨1, θ, ?_⟩
    simp only [map_one, one_mul]
    intro h
    have he : -θ = θ := by
      have hsum : θ + θ = 0 := by simpa only [two_mul, zero_mul] using congrArg (fun c : K => c * θ) h2
      exact (eq_neg_of_add_eq_zero_left hsum).symm
    exact hθ ((eq_neg_of_add_eq_zero_left h).trans he)
  · exact ⟨1, 1, by simpa only [map_one, one_mul, mul_one, one_add_one_eq_two] using h2⟩

end SymmetricSubgroupAsymptotics.CFSGPairedSquareZeroCommutant
