import SymmetricSubgroupAsymptotics.BinaryPairIntegralMixedBudget
import SymmetricSubgroupAsymptotics.BinaryPairNormalSpaceAxis
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisModels
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent

/-! The only regular-eight natural axis with relative head three and
small dimension obtains an extra actual mixed-commutator bit as soon as
the original normal has index at least eight. Index four is separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
    [MulAction.IsPretransitive F.top.range (Fin 8)]

/-- This retains the original E and its actual top image; the two space
equalities are supplied by the checked original-axis locator. -/
theorem regular_exceptional_integral_order_le_sixteen_of_index_ge_eight
    (hU : IsPGroup 2 U) (E : Subgroup U) [E.Normal]
    (htop : Nat.card F.top.range = 8)
    (himage : Nat.card (E.map F.top.rangeRestrict) = 4)
    (hindex : 8 ≤ E.index)
    (haxis : F.ambientAxis (E ⊓ F.top.ker) = BinaryRegularEightSquareCarry.K46)
    (hrad : F.ambientAxis (primeRelativeRadical 2 (E ⊓ F.top.ker)) =
      BinaryRegularEightSquareCarry.R46) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI regularExceptionalIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := E ⊓ F.top.ker
  let L := primeRelativeRadical 2 A
  have hA : A ≤ F.top.ker := inf_le_right
  have hAL : L ≤ A := primeRelativeRadical_le 2 A
  have hdA : Module.finrank (ZMod 2) (F.ambientAxis A) = 4 := by
    rw [haxis, ← BinaryRegularEightNaturalRegistry.kernel46_space,
      BinaryRegularEightNaturalRegistry.states_space]
    exact BinaryRegularEightNaturalRegistry.chart46.finrank
  have hdL : Module.finrank (ZMod 2) (F.ambientAxis L) = 1 := by
    rw [hrad, ← BinaryRegularEightNaturalRegistry.radical46_space]
    exact BinaryRegularEightNaturalRegistry.radicalChart46.finrank
  have hAc : Nat.card A = 16 := by
    have hc := F.axis_card_eq_kernel_intersection A
    rw [inf_eq_right.mpr hA] at hc
    rw [← hc]
    simpa only [Nat.card_zmod, hdA] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis A))
  have hLc : Nat.card L = 2 := by
    have hc := F.axis_card_eq_kernel_intersection L
    rw [inf_eq_right.mpr (hAL.trans hA)] at hc
    rw [← hc]
    simpa only [Nat.card_zmod, hdL] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis L))
  have hEc : Nat.card E = 64 := by
    have hc := subgroup_card_eq_map_mul_kernel_intersection F.top.rangeRestrict E
    rw [MonoidHom.ker_rangeRestrict, himage] at hc
    change Nat.card E = 4 * Nat.card A at hc
    rw [hAc] at hc
    exact hc
  have hK : 6 ≤ Module.finrank (ZMod 2) F.kernelSpace := by
    have hc := F.kernelSpace_card_mul_top
    have hk : Nat.card F.kernelSpace = 2 ^ Module.finrank (ZMod 2) F.kernelSpace := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
    rw [hk, htop] at hc
    have hi := E.card_mul_index
    rw [hEc] at hi
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show Module.finrank (ZMod 2) F.kernelSpace ≤ 5 by omega)
    norm_num at hp
    omega
  have hlarge : Nat.card (Fin 8) < 2 * Module.finrank (ZMod 2)
      (F.kernelSpace ⧸ F.normalSpace L) := by
    have hd := (F.normalSpace L).finrank_quotient_add_finrank
    rw [F.normalSpaceAxisEquiv_finrank L, hdL] at hd
    simp only [Nat.card_fin]
    omega
  have hcut : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker := by
    dsimp only [L]
    rw [primeRelativeRadical_eq_powerCommutator, primeRelativePowerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro x ⟨a, rfl⟩
      change (a : U) ^ 2 ∈ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker
      rw [F.physical_kernel_pow_two ⟨a.val, hA a.property⟩]
      exact Subgroup.one_mem _
    · exact le_inf (Subgroup.commutator_mono (show A ≤ E from inf_le_left) le_rfl)
        ((Subgroup.commutator_le_left A ⊤).trans hA)
  have hEnon : ¬ E ≤ F.top.ker := by
    intro hE
    have hbot : E.map F.top.rangeRestrict = ⊥ := by
      apply le_antisymm ?_ bot_le
      rintro y ⟨e, he, rfl⟩
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      exact hE he
    rw [hbot, Subgroup.card_bot] at himage
    omega
  have hb := F.integral_order_le_four_mul_top_of_large_mixed_cut hU (0 : Fin 8)
    E L hlarge hEnon hcut (by omega) hAc.le
  have ht : normalIntegralCoinvariantOrder (E.map F.top.rangeRestrict) ≤ 4 := by
    change (⁅E.map F.top.rangeRestrict, (⊤ : Subgroup F.top.range)⁆).relIndex
      (E.map F.top.rangeRestrict) ≤ 4
    simpa only [himage] using
      (Nat.le_of_dvd (Nat.card_pos (α := E.map F.top.rangeRestrict))
        (Subgroup.relIndex_dvd_card
          (H := ⁅E.map F.top.rangeRestrict, (⊤ : Subgroup F.top.range)⁆)
          (K := E.map F.top.rangeRestrict)))
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
