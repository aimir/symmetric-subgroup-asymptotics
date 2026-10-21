import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel

/-! Literal source, normal-image and kernel-intersection cardinalities
force the extra flip dimensions required at a large original index. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem intersection_finrank_add_two_le_kernel_of_index_ge_eight
    (E : Subgroup U) (htop : Nat.card F.top.range = 32)
    (himage : Nat.card (E.map F.top.rangeRestrict) = 16)
    (hindex : 8 ≤ E.index) :
    Module.finrank (ZMod 2) (F.ambientAxis (E ⊓ F.top.ker)) + 2 ≤
      Module.finrank (ZMod 2) F.kernelSpace := by
  let a := Module.finrank (ZMod 2) (F.ambientAxis (E ⊓ F.top.ker))
  let k := Module.finrank (ZMod 2) F.kernelSpace
  have hAc : Nat.card (E ⊓ F.top.ker : Subgroup U) = 2 ^ a := by
    have hc := F.axis_card_eq_kernel_intersection (E ⊓ F.top.ker)
    rw [inf_eq_right.mpr (show E ⊓ F.top.ker ≤ F.top.ker from inf_le_right)] at hc
    rw [← hc]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := F.ambientAxis (E ⊓ F.top.ker)))
  have hEc : Nat.card E = 16 * 2 ^ a := by
    have hc := subgroup_card_eq_map_mul_kernel_intersection F.top.rangeRestrict E
    rw [MonoidHom.ker_rangeRestrict, himage, hAc] at hc
    exact hc
  have hKc : Nat.card F.kernelSpace = 2 ^ k := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
  have hc := F.kernelSpace_card_mul_top
  rw [hKc, htop] at hc
  have hi := E.card_mul_index
  have hlo := Nat.mul_le_mul_left (Nat.card E) hindex
  rw [hi, hEc] at hlo
  change a + 2 ≤ k
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    (show k ≤ a + 1 by omega)
  rw [pow_succ] at hp
  have hpos : 0 < 2 ^ a := pow_pos (by decide) a
  nlinarith

end SymmetricSubgroupAsymptotics.BinaryPairFrame
