import SymmetricSubgroupAsymptotics.BinaryPairHalfTopIndexDimensionBudget

/-! The exact source index forces a dimension gap between the same
kernel intersection and the full kernel whenever its top image has
index two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem intersection_finrank_add_le_kernel_of_half_top_index
    (E : Subgroup U) (d : ℕ)
    (hhalf : Nat.card F.top.range = 2 * Nat.card (E.map F.top.rangeRestrict))
    (hindex : 2 ^ (d + 1) ≤ E.index) :
    Module.finrank (ZMod 2) (F.ambientAxis (E ⊓ F.top.ker)) + d ≤
      Module.finrank (ZMod 2) F.kernelSpace := by
  let a := Module.finrank (ZMod 2) (F.ambientAxis (E ⊓ F.top.ker))
  let k := Module.finrank (ZMod 2) F.kernelSpace
  let c := Nat.card (E.map F.top.rangeRestrict)
  have hcpos : 0 < c := Nat.card_pos
  have hAc : Nat.card (E ⊓ F.top.ker : Subgroup U) = 2 ^ a := by
    have hc := F.axis_card_eq_kernel_intersection (E ⊓ F.top.ker)
    rw [inf_eq_right.mpr (show E ⊓ F.top.ker ≤ F.top.ker from inf_le_right)] at hc
    rw [← hc]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := F.ambientAxis (E ⊓ F.top.ker)))
  have hEc : Nat.card E = c * 2 ^ a := by
    have hc := subgroup_card_eq_map_mul_kernel_intersection F.top.rangeRestrict E
    rw [MonoidHom.ker_rangeRestrict, hAc] at hc
    exact hc
  have hKc : Nat.card F.kernelSpace = 2 ^ k := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
  have hsource := F.kernelSpace_card_mul_top
  rw [hKc, hhalf] at hsource
  have hlo := Nat.mul_le_mul_left (Nat.card E) hindex
  rw [E.card_mul_index, hEc, ← hsource] at hlo
  have hmul : c * (2 ^ a * 2 ^ (d + 1)) ≤ c * (2 ^ k * 2) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlo
  have hb := Nat.le_of_mul_le_mul_left hmul hcpos
  have hp : 2 ^ (a + (d + 1)) ≤ 2 ^ (k + 1) := by
    simpa only [pow_add, pow_one] using hb
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  change a + d ≤ k
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
