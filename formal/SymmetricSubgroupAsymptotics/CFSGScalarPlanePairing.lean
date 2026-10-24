import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The scalar multiple of the standard alternating plane pairing is
nondegenerate exactly when its scalar is nonzero. The proof works in
characteristic two as well and uses only its two actual coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGScalarPlanePairing

variable {K : Type*} [Field K]

def pairing (k : K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) →ₗ[K] K where
  toFun u :=
    { toFun := fun v => k*(u 0*v 1-u 1*v 0)
      map_add' := by intro v w; change k*(u 0*(v 1+w 1)-u 1*(v 0+w 0)) = _; ring
      map_smul' := by intro a v; change k*(u 0*(a*v 1)-u 1*(a*v 0)) = a*(k*(u 0*v 1-u 1*v 0)); ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change k*((u 0+v 0)*w 1-(u 1+v 1)*w 0) = k*(u 0*w 1-u 1*w 0)+k*(v 0*w 1-v 1*w 0)
    ring
  map_smul' := by
    intro a u
    apply LinearMap.ext
    intro v
    change k*((a*u 0)*v 1-(a*u 1)*v 0) = a*(k*(u 0*v 1-u 1*v 0))
    ring

theorem pairing_alternating (k : K) (u : Fin 2 → K) : pairing k u u = 0 := by
  change k*(u 0*u 1-u 1*u 0) = 0
  ring

theorem pairing_separating (k : K) (hk : k ≠ 0) (u : Fin 2 → K)
    (hu : ∀ v, pairing k u v = 0) : u = 0 := by
  have h0 := hu ![(0 : K),1]
  change k*(u 0*1-u 1*0) = 0 at h0
  simp only [mul_one,mul_zero,sub_zero] at h0
  have hu0 : u 0 = 0 := (mul_eq_zero.mp h0).resolve_left hk
  have h1 := hu ![(1 : K),0]
  change k*(u 0*0-u 1*1) = 0 at h1
  simp only [mul_zero,mul_one,zero_sub] at h1
  have hu1 : u 1 = 0 := neg_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hk)
  funext i
  fin_cases i
  · exact hu0
  · exact hu1

theorem pairing_full (k : K) (hk : k ≠ 0) (u : Fin 2 → K) (hu : u ≠ 0) :
    Function.Surjective (pairing k u) := by
  have hn : ∃ v, pairing k u v ≠ 0 := by
    by_contra hn
    apply hu
    apply pairing_separating k hk u
    intro v
    exact not_not.mp (fun hv => hn ⟨v,hv⟩)
  obtain ⟨v,hv⟩ := hn
  intro a
  refine ⟨(a/pairing k u v) • v,?_⟩
  rw [map_smul]
  change (a/pairing k u v)*pairing k u v = a
  exact div_mul_cancel₀ a hv

end SymmetricSubgroupAsymptotics.CFSGScalarPlanePairing
