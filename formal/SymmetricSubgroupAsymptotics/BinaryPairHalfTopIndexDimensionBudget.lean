import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel

/-! An actual half-order top image and original normal index at least
eight force two extra dimensions in the SAME correlated binary kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem intersection_finrank_add_two_le_kernel_of_half_top_index_eight
    (E : Subgroup U)
    (hhalf : Nat.card F.top.range = 2 * Nat.card (E.map F.top.rangeRestrict))
    (hindex : 8 ≤ E.index) :
    Module.finrank (ZMod 2) (F.ambientAxis (E ⊓ F.top.ker)) + 2 ≤
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
  have hmul : c * (2 ^ a * 8) ≤ c * (2 ^ k * 2) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlo
  have hb : 2 ^ a * 8 ≤ 2 ^ k * 2 := Nat.le_of_mul_le_mul_left hmul hcpos
  change a + 2 ≤ k
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show k ≤ a + 1 by omega)
  rw [pow_succ] at hp
  have hpos : 0 < 2 ^ a := pow_pos (by decide) a
  nlinarith

end SymmetricSubgroupAsymptotics.BinaryPairFrame
