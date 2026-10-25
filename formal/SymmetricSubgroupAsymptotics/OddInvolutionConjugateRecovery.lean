import Mathlib.Algebra.Group.Subgroup.Basic

/-! An actual odd product of two involutions recovers one involution
from the other and its conjugate. This is a literal group-word identity;
no dihedral-group recognition or element-order completeness is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OddInvolutionConjugateRecovery
variable {G : Type*} [Group G]

/-- If `t*s` has an odd period, the two conjugate involutions `s` and
`t*s*t` recover `t` by this exact word. -/
theorem recovery (t s : G) (k : ℕ) (ht : t ^ 2 = 1) (hs : s ^ 2 = 1)
    (hodd : (t * s) ^ (2 * k + 1) = 1) :
    t = s * ((t * s * t) * s) ^ k := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hpower : (t * s) ^ (2 * k) = (t * s)⁻¹ := by
    have he : (t * s) ^ (2 * k) * (t * s) = (t * s)⁻¹ * (t * s) := by
      rw [← pow_succ, hodd, inv_mul_cancel]
    exact mul_right_cancel he
  have hpair : (t * s * t) * s = (t * s) ^ 2 := by
    simp only [pow_two, mul_assoc]
  symm
  calc
    s * ((t * s * t) * s) ^ k = s * (t * s) ^ (2 * k) := by
      rw [hpair, ← pow_mul]
    _ = s * (t * s)⁻¹ := by rw [hpower]
    _ = t := by
      rw [mul_inv_rev, hsi, ← mul_assoc, ← pow_two, hs, one_mul, hti]

/-- Membership is retained in the actual original subgroup. -/
theorem mem_of_conjugate (H : Subgroup G) (t s : G) (k : ℕ)
    (ht : t ^ 2 = 1) (hs : s ^ 2 = 1)
    (hodd : (t * s) ^ (2 * k + 1) = 1)
    (hsmem : s ∈ H) (hconj : t * s * t ∈ H) : t ∈ H := by
  rw [recovery t s k ht hs hodd]
  exact H.mul_mem hsmem (H.pow_mem (H.mul_mem hconj hsmem) k)

end SymmetricSubgroupAsymptotics.OddInvolutionConjugateRecovery
