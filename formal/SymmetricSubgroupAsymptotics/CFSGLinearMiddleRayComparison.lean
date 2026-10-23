import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Comparing two image rays and their fixed middle-zero difference
forces their normalized middle ratios to coincide. This is pure linear
algebra, without any field or geometric reconstruction premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearMiddleRayComparison
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem middle_ratios_eq (projection : V →ₗ[K] V) (coordinate : V →ₗ[K] K)
    (p q h E F : V) (hpq : LinearIndependent K ![p,q])
    (hp : projection p = p) (hq : projection q = q) (hh : projection h = 0)
    (hcp : coordinate p = 0) (hcq : coordinate q = 0) (hch : coordinate h = 1)
    (a b r s k : K) (ha : a ≠ 0)
    (hE : E = a • (p + r • h)) (hF : F = b • (q + s • h))
    (hfix : E - F = k • (p - q)) : r = s := by
  rw [hE,hF] at hfix
  have hproj := congrArg projection hfix
  simp only [map_sub, map_smul, map_add, hp, hq, hh, smul_zero, add_zero] at hproj
  have he : (a - k) • p + (k - b) • q = 0 := by
    calc
      _ = (a • p - b • q) - k • (p - q) := by module
      _ = 0 := sub_eq_zero.mpr hproj
  obtain ⟨hak,hkb⟩ := LinearIndependent.pair_iff.mp hpq (a-k) (k-b) he
  have hab : a = b := (sub_eq_zero.mp hak).trans (sub_eq_zero.mp hkb)
  have hmid := congrArg coordinate hfix
  simp only [map_sub, map_smul, map_add, hcp, hcq, hch, smul_eq_mul,
    mul_one, zero_add, sub_self, mul_zero] at hmid
  have hprod : a * (r - s) = 0 := by
    calc
      _ = a * r - b * s := by rw [←hab]; ring
      _ = 0 := hmid
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha)

end SymmetricSubgroupAsymptotics.CFSGLinearMiddleRayComparison
