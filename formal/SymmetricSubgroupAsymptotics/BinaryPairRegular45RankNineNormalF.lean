import SymmetricSubgroupAsymptotics.BinaryPairRegularThreeHeadSectors
import SymmetricSubgroupAsymptotics.BinaryPairInnerThreeAxisBounds
import SymmetricSubgroupAsymptotics.BinaryPairRankAdditiveKernelNormalPacket
import SymmetricSubgroupAsymptotics.BinarySixteenHeadThreeTopJoint
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel
import SymmetricSubgroupAsymptotics.BinaryRegular45TwelveNormalF
import SymmetricSubgroupAsymptotics.BinaryPairAugmentationSmallOrderNormalF
import SymmetricSubgroupAsymptotics.BinaryPairRegularAugmentationPreimage

/-! Complete actual regular45 sector at rank nine. Every small-kernel
case uses the proved uniform subaxis capacity three. The only large
original kernels are the twelve-space and augmentation; their exceptional
small denominators use the actual interval normal-F construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance regular45RankNineNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem regular45_rank_nine_derived_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hthree : MarkedC4.normalGen F.top.ker=3) (hsix : MarkedC4.genRank F.top.range=6)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 45).2.space)
    (N : Subgroup U) [N.Normal] (hND : N≤commutator U)
    (hnonab : ¬∀ a b : U ⧸ N,a*b=b*a) :
    ∃ D : Subgroup (U ⧸ N),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  letI : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  have hTop := F.top_isPGroup hU
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [←F.axisNatural_normalGen F.top.ker le_rfl hU,hthree] <;> omega
  have hWspace : W.toSubmodule=F.kernelSpace := F.original_ambientAxis_kernel
  have hbound (A : Subgroup U) [A.Normal] (hA : A≤F.top.ker) : MarkedC4.normalGen A≤3 :=
    F.normalGen_le_three_of_inner_regular45 E hU hH hJ A hA
  have hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range := by omega
  have hquotjoint (M : Subgroup F.top.range) [M.Normal] :
      Nat.card (commutator (F.top.range ⧸ M))*
        Nat.card (Subgroup.center (F.top.range ⧸ M))≤2^8 :=
    E.sixteen_rank_six_head_three_all_quotient_joint_le_256 hTop (by omega) W hhead M
  have hJdim : Module.finrank (ZMod 2) E.kernelSpace=7 := by
    rw [hJ]
    exact (BinaryRegularEightNaturalRegistry.charts 45).2.finrank
  have hD := E.sixteen_rank_six_head_three_derived_card_le_sixteen hTop (by omega) W hhead
  have hZ := E.original_center_le_two_of_large_kernel hTop (by omega)
  have hsourcejoint : Nat.card (commutator F.top.range)*
      Nat.card (Subgroup.center F.top.range)≤2^5 :=
    (Nat.mul_le_mul hD hZ).trans (by norm_num)
  have hcardOfDim (k : ℕ) (hd : Module.finrank (ZMod 2) F.kernelSpace≤k) :
      Nat.card F.kernelSpace≤2^k := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
    rw [Nat.card_zmod] at he
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0<2) hd
  have hfinish (hN : N≤F.top.ker)
      (himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^11) :
      ∃ D : Subgroup (U ⧸ N),D.Normal ∧
        MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
          MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 :=
    F.rank_nine_rank_additive_kernel_normalF_packet hU hrank hadd 3 11 5 hbound
      hsourcejoint (by omega) N hN hND himage hnonab
  by_cases hN : N≤F.top.ker
  · by_cases hsmallK : Module.finrank (ZMod 2) F.kernelSpace≤11
    · apply hfinish hN
      exact F.large_kernel_normal_image_card_le N hN 1 (2^11) (2^11) (by
        have hp : 0<Nat.card N := Nat.card_pos
        omega) (hcardOfDim 11 hsmallK) (by simp)
    obtain ⟨hLow,h45 | h46⟩ := E.regular45_head_three_large_dimension_layers hTop hH hJ W hhead (by
      rw [hWspace]
      omega)
    · have hAug := regular45_full_lower_kernel_eq_augmentation F E h45 hLow
      by_cases hsmallN : Nat.card N≤8
      · exact F.augmentation_small_order_normalF_packet E hU hAug (by omega) N hsmallN
      have hNcard : 16≤Nat.card N := by
        obtain ⟨k,hk⟩ := (hU.to_subgroup N).exists_card_eq
        have hfour : 4≤k := by
          by_contra hh
          have hb := Nat.pow_le_pow_right (by decide : 0<2) (show k≤3 from by omega)
          rw [←hk] at hb
          norm_num at hb
          omega
        rw [hk]
        exact Nat.pow_le_pow_right (by decide : 0<2) hfour
      have hKdim : Module.finrank (ZMod 2) F.kernelSpace=15 := by
        have hd := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (0 : Fin 16)
        rw [←hAug] at hd
        norm_num only [Nat.card_fin] at hd
        omega
      apply hfinish hN
      exact F.large_kernel_normal_image_card_le N hN 16 (2^15) (2^11) hNcard
        (hcardOfDim 15 hKdim.le) (by norm_num)
    · by_cases hbot : N=⊥
      · subst N
        exact F.regular45_twelve_zero_normalF_packet E hU hH hJ h46 hLow
      have hKdim : Module.finrank (ZMod 2) F.kernelSpace=12 := by
        have hd := E.pairModuleLayers_finrank W
        rw [hWspace,h46,hLow,(BinaryRegularEightNaturalRegistry.charts 46).2.finrank] at hd
        have hLdim : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin 8 → ZMod 2))=8 := by simp
        have hd46 : (BinaryRegularEightNaturalRegistry.charts 46).1=4 := rfl
        rw [hLdim,hd46] at hd
        omega
      apply hfinish hN
      exact F.large_kernel_normal_image_card_le N hN 2 (2^12) (2^11)
        (N.one_lt_card_iff_ne_bot.mpr hbot) (hcardOfDim 12 hKdim.le) (by norm_num)
  · have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^8 := by
      simpa using F.moving_normal_kernel_image_card_le_half hU (0 : Fin 16) N hN
    exact F.rank_nine_rank_additive_joint_normalF_packet hU hrank hadd 3 8 8 hbound
      hquotjoint (by omega) N hND himage hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
