import SymmetricSubgroupAsymptotics.BinaryPairAugmentationSmallNormalF
import SymmetricSubgroupAsymptotics.BinaryPairNormalSpaceAxis
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds

/-! The augmentation construction applies to every original normal of
order at most eight. Its zero top image is DERIVED from the large actual
kernel section, rather than added to the final hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance augmentationSmallOrderNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]

theorem augmentation_small_order_normalF_packet
    (hU : IsPGroup 2 U)
    (hK : F.kernelSpace=PermutationAugmentation.space (ZMod 2) (Fin 16))
    (hJ : 3≤Module.finrank (ZMod 2) E.kernelSpace)
    (N : Subgroup U) [N.Normal] (hcard : Nat.card N≤8) :
    ∃ D : Subgroup (U ⧸ N),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have ha : Nat.card (F.ambientAxis N)≤8 := by
    rw [F.axis_card_eq_kernel_intersection N]
    exact (Subgroup.card_le_of_le (show F.top.ker⊓N≤N from inf_le_right)).trans hcard
  have hpow : 2^Module.finrank (ZMod 2) (F.ambientAxis N)≤8 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis N)
    rw [Nat.card_zmod] at he
    rwa [he] at ha
  have hsmall : Module.finrank (ZMod 2) (F.ambientAxis N)≤3 := by
    by_contra hh
    have hb := Nat.pow_le_pow_right (by decide : 0<2)
      (show 4≤Module.finrank (ZMod 2) (F.ambientAxis N) from by omega)
    norm_num at hb
    omega
  have hdK : Module.finrank (ZMod 2) F.kernelSpace=15 := by
    have hd := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (0 : Fin 16)
    rw [←hK] at hd
    norm_num only [Nat.card_fin] at hd
    omega
  have hdim := (F.normalSpace N).finrank_quotient_add_finrank
  rw [F.normalSpaceAxisEquiv_finrank,hdK] at hdim
  have hN : N≤F.top.ker := F.normal_le_top_ker_of_large N hU (0 : Fin 16) (by
    norm_num only [Nat.card_fin]
    omega)
  exact F.augmentation_small_axis_normalF_packet E hU hK hJ N hN hsmall

end SymmetricSubgroupAsymptotics.BinaryPairFrame
