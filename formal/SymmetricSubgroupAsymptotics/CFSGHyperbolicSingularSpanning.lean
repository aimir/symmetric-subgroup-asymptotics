import SymmetricSubgroupAsymptotics.CFSGHyperbolicPlaneProjection
import Mathlib.Tactic.Push

/-! An actual hyperbolic pair makes the singular vectors span: a
linear functional vanishing on every singular vector is zero. A genuine
nonzero singular vector in a nondegenerate symmetric space supplies
such a pair by an explicit correction. No finite-field count is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicSingularSpanning
open CFSGHyperbolicPlaneProjection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

theorem norm_sub_singular (hs : ∀ x y, B x y = B y x) (e z : V)
    (he : B e e = 0) (t : K) :
    B (z - t • e) (z - t • e) = B z z - 2 * t * B e z := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, he, mul_zero, sub_zero, hs z e]
  ring

theorem exists_hyperbolic_partner (h2 : (2 : K) ≠ 0)
    (hs : ∀ x y, B x y = B y x)
    (hn : ∀ e, (∀ x, B e x = 0) → e = 0) (e : V) (he : e ≠ 0) (he0 : B e e = 0) :
    ∃ f : V, B f f = 0 ∧ B e f ≠ 0 := by
  classical
  have hz : ∃ z, B e z ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (hn e h)
  obtain ⟨z, hz⟩ := hz
  let t := B z z / (2 * B e z)
  refine ⟨z - t • e, ?_, ?_⟩
  · rw [norm_sub_singular B hs e z he0]
    dsimp [t]
    field_simp [h2, hz] <;> ring
  · simpa only [map_sub, map_smul, smul_eq_mul, he0, mul_zero, sub_zero] using hz

theorem functional_eq_zero_of_singular (h2 : (2 : K) ≠ 0)
    (hs : ∀ x y, B x y = B y x) (e f : V)
    (he : B e e = 0) (hf : B f f = 0) (hc : B e f ≠ 0)
    (l : V →ₗ[K] K) (hl : ∀ x, B x x = 0 → l x = 0) : l = 0 := by
  have hle : l e = 0 := hl e he
  have hlf : l f = 0 := hl f hf
  apply LinearMap.ext
  intro x
  let z := projection B e f x
  have hz := projection_mem B hs e f he hf hc x
  have hze : B z e = 0 := (hs z e).trans hz.1
  have hzf : B z f = 0 := (hs z f).trans hz.2
  let t := -(B z z / (2 * B e f))
  have hw : B (z + e + t • f) (z + e + t • f) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, he, hf, hze, hzf, hs e z, hs f z, hs f e,
      mul_zero, zero_add, add_zero]
    dsimp [t]
    field_simp [h2, hc] <;> ring
  have hlz : l z = 0 := by
    have hh := hl (z + e + t • f) hw
    simpa only [map_add, map_smul, smul_eq_mul, hle, hlf, mul_zero, add_zero] using hh
  have hzx : l z = l x := by
    change l (projection B e f x) = l x
    rw [projection_apply]
    simp only [map_sub, map_smul, smul_eq_mul, hle, hlf, mul_zero, sub_zero]
  exact hzx.symm.trans hlz

theorem exists_singular_not_killed (h2 : (2 : K) ≠ 0)
    (hs : ∀ x y, B x y = B y x) (e f : V)
    (he : B e e = 0) (hf : B f f = 0) (hc : B e f ≠ 0)
    (l : V →ₗ[K] K) (hl : l ≠ 0) : ∃ x, B x x = 0 ∧ l x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  exact hl (functional_eq_zero_of_singular B h2 hs e f he hf hc l h)

end SymmetricSubgroupAsymptotics.CFSGHyperbolicSingularSpanning
