import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexDeterminant
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter

/-! The actual odd-dimensional B elementary group has trivial centre
in odd positive characteristic. Its scalar centre preserves the actual
Gram form and has determinant one; both conditions use the SAME matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCenter
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm CFSGOrthogonalBIndexDeterminant
variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

include p in
theorem center_eq_bot (h2 : (2 : K) ≠ 0) (r : ℕ) :
    Subgroup.center (elementaryRootGroup K (r + 1)) = ⊥ := by
  apply bot_unique
  intro u hu
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r h2 u).mp hu
  have hf := elementary_le_formUnits h2 (r + 1) u.property
  change (u.val : Mat K (r + 1)).transpose * gram K (r + 1) *
    (u.val : Mat K (r + 1)) = gram K (r + 1) at hf
  rw [hc, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul] at hf
  have hcc := congrArg (fun M : Mat K (r + 1) => M (middle (r + 1)) (middle (r + 1))) hf
  have hsq : c ^ 2 = 1 := by
    simpa only [Matrix.smul_apply, smul_eq_mul, gram, middle, mul_one, pow_two] using hcc
  have hd := elementary_det_eq_one K p (r + 1) u
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  have hd' : c ^ (2 * (r + 1) + 1) = 1 := by
    simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique, two_mul] using hd
  have hc1 : c = 1 := by
    have he : c ^ (2 * (r + 1) + 1) = c := by
      rw [pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
    exact he.symm.trans hd'
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1, one_smul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCenter
