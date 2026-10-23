import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! An anisotropic projection and a nonzero singular direction are
independent. Adding that direction bypasses every proportional projection,
with the coefficient of the original direction kept explicitly nonzero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_anisotropic_singular_independent (sigma : K ≃+* K) (H : Matrix I I K)
    (x u : I → K) (hx : hermitianPair sigma H x x ≠ 0) (hu : u ≠ 0)
    (hnu : hermitianPair sigma H u u = 0) : LinearIndependent K ![x,u] := by
  have hx0 : x ≠ 0 := by
    intro h
    exact hx (by rw [h]; exact pair_zero_left _ _ _)
  apply (LinearIndependent.pair_iff' hx0).mpr
  intro c he
  have hc : c ≠ 0 := by
    intro h
    exact hu (by simpa only [h, zero_smul] using he.symm)
  have hn := hermitianPair_smul sigma H c c x x
  rw [he, hnu] at hn
  have hsc : sigma c ≠ 0 := fun h => hc (sigma.injective (h.trans (map_zero _).symm))
  exact (mul_ne_zero (mul_ne_zero hsc hc) hx) hn.symm

theorem independent_add_proportional {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (x u : V) (hxu : LinearIndependent K ![x,u]) (c : K) (hc : c ≠ 0) :
    LinearIndependent K ![x + u,c • x] := by
  apply LinearIndependent.pair_iff.mpr
  intro a b hab
  have he : (a + b * c) • x + a • u = 0 := by
    calc
      _ = a • (x + u) + b • (c • x) := by module
      _ = 0 := hab
  obtain ⟨hax, ha⟩ := LinearIndependent.pair_iff.mp hxu (a + b * c) a he
  refine ⟨ha, ?_⟩
  have hbc : b * c = 0 := by simpa only [ha, zero_add] using hax
  exact (mul_eq_zero.mp hbc).resolve_right hc

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
