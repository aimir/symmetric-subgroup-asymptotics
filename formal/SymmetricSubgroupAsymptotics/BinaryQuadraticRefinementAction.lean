import SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTorsor
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! The literal contragredient actions on fixed-polar quadratic forms
and on the dual have the same linear part. The affine translation is the
actual change of the chosen reference form. No invariant reference form
or split action is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementAction
open BinaryQuadraticRefinementTorsor

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

abbrev dualAction (ρ : G →* (V ≃ₗ[K] V)) : DistribMulAction G (Module.Dual K V) where
  smul g f := f.comp (ρ g⁻¹).toLinearMap
  one_smul f := by
    apply LinearMap.ext
    intro x
    change f (ρ (1 : G)⁻¹ x) = f x
    rw [inv_one, map_one]
    rfl
  mul_smul g h f := by
    apply LinearMap.ext
    intro x
    change f (ρ (g*h)⁻¹ x) = f (ρ h⁻¹ (ρ g⁻¹ x))
    rw [mul_inv_rev, map_mul]
    rfl
  smul_zero g := by
    apply LinearMap.ext
    intro x
    rfl
  smul_add g f h := by
    apply LinearMap.ext
    intro x
    rfl

abbrev refinementAction (Q₀ : QuadraticForm K V) (ρ : G →* (V ≃ₗ[K] V))
    (hρ : ∀ g : G, ∀ x y : V,
      Q₀.polarBilin (ρ g x) (ρ g y) = Q₀.polarBilin x y) :
    MulAction G (Refinement Q₀) where
  smul g Q := pullback Q₀ (ρ g⁻¹) (hρ g⁻¹) Q
  one_smul Q := by
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    change Q.val (ρ (1 : G)⁻¹ x) = Q.val x
    rw [inv_one, map_one]
    rfl
  mul_smul g h Q := by
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    change Q.val (ρ (g*h)⁻¹ x) = Q.val (ρ h⁻¹ (ρ g⁻¹ x))
    rw [mul_inv_rev, map_mul]
    rfl

variable [Finite K] (hK : Nat.card K = 2) (Q₀ : QuadraticForm K V)
    (ρ : G →* (V ≃ₗ[K] V))
    (hρ : ∀ g : G, ∀ x y : V,
      Q₀.polarBilin (ρ g x) (ρ g y) = Q₀.polarBilin x y)

def translation (g : G) : Module.Dual K V :=
  difference hK Q₀ (pullback Q₀ (ρ g⁻¹) (hρ g⁻¹) ⟨Q₀, rfl⟩)

theorem same_linear_part (g : G) (Q : Refinement Q₀) :
    letI := dualAction ρ
    letI := refinementAction Q₀ ρ hρ
    refinementEquivDual hK Q₀ (g • Q) =
      translation hK Q₀ ρ hρ g + g • refinementEquivDual hK Q₀ Q :=
  pullback_affine hK Q₀ (ρ g⁻¹) (hρ g⁻¹) Q

omit [Finite K] in
theorem stabilizer_mem_iff (Q : Refinement Q₀) (g : G) :
    letI := refinementAction Q₀ ρ hρ
    g ∈ MulAction.stabilizer G Q ↔ ∀ x : V, Q.val (ρ g x) = Q.val x := by
  letI := refinementAction Q₀ ρ hρ
  change pullback Q₀ (ρ g⁻¹) (hρ g⁻¹) Q = Q ↔ _
  rw [pullback_fixed_iff]
  constructor
  · intro h x
    have hx := h (ρ g x)
    have hi : ρ g⁻¹ (ρ g x) = x := by
      rw [map_inv]
      exact (ρ g).symm_apply_apply x
    rw [hi] at hx
    exact hx.symm
  · intro h x
    have hx := h (ρ g⁻¹ x)
    have hi : ρ g (ρ g⁻¹ x) = x := by
      rw [map_inv]
      exact (ρ g).apply_symm_apply x
    rw [hi] at hx
    exact hx.symm

end SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementAction
