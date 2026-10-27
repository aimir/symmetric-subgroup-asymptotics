import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-! Inverting a cyclic generator normalizes its whole cyclic subgroup.
No finite order or coprimality premise is required. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ConjugateInverseCyclicNormalizerWitness
variable {G : Type*} [Group G]

private theorem conjugate_mem (sigma a : G) (ha : sigma*a*sigma⁻¹=a⁻¹)
    (z : G) (hz : z ∈ Subgroup.zpowers a) :
    sigma*z*sigma⁻¹ ∈ Subgroup.zpowers a := by
  obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  change (MulAut.conj sigma) (a^k) ∈ Subgroup.zpowers a
  rw [map_zpow]
  change (sigma*a*sigma⁻¹)^k ∈ Subgroup.zpowers a
  rw [ha]
  exact (Subgroup.zpowers a).zpow_mem
    ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)) k

theorem mem_normalizer_zpowers (sigma a : G) (ha : sigma*a*sigma⁻¹=a⁻¹) :
    sigma ∈ Subgroup.normalizer ((Subgroup.zpowers a) : Set G) := by
  have hb : sigma⁻¹*a*sigma=a⁻¹ := by
    calc
      sigma⁻¹*a*sigma = sigma⁻¹*(sigma*a*sigma⁻¹)⁻¹*sigma := by rw [ha,inv_inv]
      _ = a⁻¹ := by group
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · exact conjugate_mem sigma a ha z
  · intro hz
    have hi : sigma⁻¹*a*(sigma⁻¹)⁻¹=a⁻¹ := by simpa only [inv_inv] using hb
    have hh := conjugate_mem sigma⁻¹ a hi (sigma*z*sigma⁻¹) hz
    simpa [mul_assoc] using hh

end SymmetricSubgroupAsymptotics.ConjugateInverseCyclicNormalizerWitness
