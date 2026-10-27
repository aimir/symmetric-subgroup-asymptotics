import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Conj

/-! Two literal power-conjugacy identities certify cyclic-normalizer
membership, without any order or coprimality premise. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AmbientCyclePowerNormalizerWitness
variable {G : Type*} [Group G]

theorem conjugate_mem_zpowers_of_power (sigma a : G) (r : ℕ)
    (hpower : sigma*a*sigma⁻¹=a^r) (z : G) (hz : z ∈ Subgroup.zpowers a) :
    sigma*z*sigma⁻¹ ∈ Subgroup.zpowers a := by
  obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  change (MulAut.conj sigma) (a^k) ∈ Subgroup.zpowers a
  rw [map_zpow]
  change (sigma*a*sigma⁻¹)^k ∈ Subgroup.zpowers a
  rw [hpower]
  exact (Subgroup.zpowers a).zpow_mem
    ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) r) k

theorem mem_normalizer_zpowers (sigma a : G) (r s : ℕ)
    (hforward : sigma*a*sigma⁻¹=a^r)
    (hinverse : sigma⁻¹*a*sigma=a^s) :
    sigma ∈ Subgroup.normalizer ((Subgroup.zpowers a) : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · exact conjugate_mem_zpowers_of_power sigma a r hforward z
  · intro hz
    have hi : sigma⁻¹*a*(sigma⁻¹)⁻¹=a^s := by simpa only [inv_inv] using hinverse
    have hh := conjugate_mem_zpowers_of_power sigma⁻¹ a s hi (sigma*z*sigma⁻¹) hz
    simpa [mul_assoc] using hh

end SymmetricSubgroupAsymptotics.AmbientCyclePowerNormalizerWitness
