import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Displacement images for an actual group representation by linear
equivalences. Conjugation transports the SAME image submodule. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearConjugateDisplacement
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def displacement (rho : G →* (V ≃ₗ[K] V)) (g : G) : V →ₗ[K] V :=
  (rho g).toLinearMap - LinearMap.id

theorem conjugate_apply (rho : G →* (V ≃ₗ[K] V)) (g h : G) (v : V) :
    displacement rho (g * h * g⁻¹) v = rho g (displacement rho h ((rho g).symm v)) := by
  change rho (g * h * g⁻¹) v - v = rho g (rho h ((rho g).symm v) - (rho g).symm v)
  rw [map_mul, map_mul, map_inv]
  change rho g (rho h ((rho g).symm v)) - v = _
  rw [map_sub, LinearEquiv.apply_symm_apply]

theorem conjugate_range (rho : G →* (V ≃ₗ[K] V)) (g h : G) :
    LinearMap.range (displacement rho (g * h * g⁻¹)) =
      (LinearMap.range (displacement rho h)).map (rho g).toLinearMap := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨displacement rho h ((rho g).symm v), ⟨(rho g).symm v, rfl⟩, ?_⟩
    exact (conjugate_apply rho g h v).symm
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    refine ⟨rho g v, ?_⟩
    rw [conjugate_apply, LinearEquiv.symm_apply_apply]
    rfl

end SymmetricSubgroupAsymptotics.CFSGLinearConjugateDisplacement
