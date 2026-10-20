import SymmetricSubgroupAsymptotics.BinaryFanoHeptadData
import SymmetricSubgroupAsymptotics.AffineIrreducibleConjugation

/-! Fifteen displayed words give the nonzero orbit in the original row20
coordinates. They are the two seven-orbits of beta and its fixed vector,
joined by alpha. No search through the linear group is involved. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFanoHeptadNonzeroOrbit

open BinaryFourAffineImage BinaryFanoHeptadData

def seed : Vector := pointEquiv.symm 8

def sevenExponent (i : Fin 16) : ℕ :=
  ![0, 6, 1, 2, 0, 4, 5, 3, 0, 6, 1, 2, 0, 4, 5, 3] i

def threeExponent (i : Fin 16) : ℕ :=
  ![0, 1, 1, 2, 1, 2, 2, 1, 0, 2, 2, 1, 2, 1, 1, 2] i

def word (i : Fin 16) : LinearGroup := b20 ^ sevenExponent i * a20 ^ threeExponent i

theorem word_seed : ∀ i : Fin 16, i ≠ 0 → linearPerm (word i) 8 = i := by
  intro i
  fin_cases i <;> decide +kernel

theorem pointEquiv_zero : pointEquiv (0 : Vector) = 0 := by decide +kernel

theorem word_mem (R : Subgroup LinearGroup) (ha : a20 ∈ R) (hb : b20 ∈ R)
    (i : Fin 16) : word i ∈ R :=
  R.mul_mem (R.pow_mem hb _) (R.pow_mem ha _)

theorem seed_orbit (R : Subgroup LinearGroup) (ha : a20 ∈ R) (hb : b20 ∈ R)
    (x : Vector) (hx : x ≠ 0) : ∃ g ∈ R, g seed = x := by
  have hi : pointEquiv x ≠ 0 := by
    intro he
    exact hx (pointEquiv.injective (he.trans pointEquiv_zero.symm))
  refine ⟨word (pointEquiv x), word_mem R ha hb _, ?_⟩
  apply pointEquiv.injective
  exact word_seed (pointEquiv x) hi

theorem irreducible_of_seed_orbit (R : Subgroup LinearGroup) (v : Vector)
    (horbit : ∀ x : Vector, x ≠ 0 → ∃ g ∈ R, g v = x) :
    AffineModel.Irreducible R := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  obtain ⟨g, hg, hgv⟩ := horbit x hx0
  have hv : v ∈ S := by
    have hh := hS g⁻¹ (R.inv_mem hg) x hx
    rw [← hgv] at hh
    change g.symm (g v) ∈ S at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  apply top_unique
  intro y _hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact S.zero_mem
  obtain ⟨k, hk, hkv⟩ := horbit y hy0
  rw [← hkv]
  exact hS k hk v hv

theorem irreducible (R : Subgroup LinearGroup) (ha : a20 ∈ R) (hb : b20 ∈ R) :
    AffineModel.Irreducible R :=
  irreducible_of_seed_orbit R seed (seed_orbit R ha hb)

end BinaryFanoHeptadNonzeroOrbit
end SymmetricSubgroupAsymptotics

end
