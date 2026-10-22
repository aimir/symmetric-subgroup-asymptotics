import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

/-! A kernel fixing one vector fixes its entire actual orbit. If that
orbit consists of all nonzero vectors, a faithful linear representation
forces the original kernel to be trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalKernelFixedVector
variable {G H K V : Type*} [Group G] [Group H] [Field K]
  [AddCommGroup V] [Module K V]

theorem kernel_eq_bot (f : G →* H) (rho : G →* (V ≃ₗ[K] V))
    (hrho : Function.Injective rho) (v : V)
    (hfix : ∀ g ∈ f.ker, rho g v = v)
    (horbit : ∀ w : V, w ≠ 0 → ∃ h : G, rho h v = w) : f.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply hrho
  rw [map_one]
  apply LinearEquiv.ext
  intro w
  by_cases hw : w = 0
  · subst w
    exact map_zero (rho g)
  · obtain ⟨h, hh⟩ := horbit w hw
    have hconj : h⁻¹ * g * h ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      have hfg := MonoidHom.mem_ker.mp hg
      simp only [map_mul, map_inv, hfg, mul_one, inv_mul_cancel]
    have he : rho g * rho h = rho h * rho (h⁻¹ * g * h) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc
      rho g w = (rho g * rho h) v := by
        change rho g w = rho g (rho h v)
        rw [hh]
      _ = (rho h * rho (h⁻¹ * g * h)) v := congrArg (fun a : V ≃ₗ[K] V => a v) he
      _ = rho h v := by change rho h (rho (h⁻¹ * g * h) v) = _; rw [hfix _ hconj]
      _ = w := hh

end SymmetricSubgroupAsymptotics.CFSGNormalKernelFixedVector
