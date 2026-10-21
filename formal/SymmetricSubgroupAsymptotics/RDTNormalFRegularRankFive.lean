import SymmetricSubgroupAsymptotics.RDTNormalFRegularMiddleKernel
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels
import SymmetricSubgroupAsymptotics.NormalFPacketCoefficientMono
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK24SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK26SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK27SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK28SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK29SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK30SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK31SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK32SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK33SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK34SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK35SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK36SmallAxisCover
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK37SmallAxisCover

/-! Every original regular-eight top of rank at least five, with all
original normal quotients. A single linear-axis installer handles all
middle kernels; the augmentation kernel uses the independent joint
bound and all small kernels use the uniform order theorem. No sixteen-
point subgroup or affine lift census is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryRegularEightNaturalRegistry
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem regular_all_kernel_models_with_head (hU : IsPGroup 2 U)
    (hH : F.top.range=H) :
    ∃ i : Fin 47, F.kernelSpace=(charts i).2.space ∧
      MarkedC4.normalGen F.top.ker ≤ headCeiling i := by
  let W := F.literalTopAxis H hH F.top.ker
  obtain ⟨i,hi⟩ := complete W
  have hs : W.toSubmodule=F.kernelSpace :=
    (F.literalTopAxis_space H hH F.top.ker).trans F.ambientAxis_kernel
  have hh : MarkedC4.normalGen F.top.ker =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    (F.axis_normalGen_eq_coinvariants F.top.ker le_rfl hU).trans
      (F.literalTopAxis_head H hH F.top.ker).symm
  refine ⟨i,hs.symm.trans ((congrArg Subrepresentation.toSubmodule hi.symm).trans
    (states_space i)),?_⟩
  rw [hh,←hi]
  exact coinvariants_finrank_le i

theorem regular_rank_five_all_normal_quotients_unit
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) (hH : F.top.range=H)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N,a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N),W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have ht : Nat.card F.top.range=8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  obtain ⟨i,hK,hhead⟩ := F.regular_all_kernel_models_with_head hU hH
  fin_cases i
  · change F.kernelSpace=chart0.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart0.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change MarkedC4.normalGen F.top.ker ≤ 1 at hhead
    have hTop := F.top_isPGroup hU
    letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
    have hp := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card
      (⊤ : Subgroup F.top.range)
    rw [Subgroup.card_top,ht] at hp
    have hntop : MarkedC4.normalGen (⊤ : Subgroup F.top.range) ≤ 3 :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
    have htop := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans hntop
    have hu := F.genRank_le_actual_pair_kernel_add_top
    omega
  · change F.kernelSpace=chart2.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart2.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart3.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart3.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart4.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart4.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart5.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart5.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart6.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart6.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart7.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart7.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart8.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart8.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart9.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart9.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart10.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart10.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart11.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart11.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart12.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart12.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart13.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart13.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart14.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart14.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart15.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart15.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart16.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart16.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart17.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart17.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart18.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart18.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart19.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart19.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart20.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart20.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart21.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart21.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart22.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart22.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart23.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart23.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart24.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart24 hK.symm
      BinaryRegularRankFiveK24SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart25.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart25 hK.symm
      BinaryRegularRankFiveK25SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart26.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart26 hK.symm
      BinaryRegularRankFiveK26SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart27.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart27 hK.symm
      BinaryRegularRankFiveK27SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart28.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart28 hK.symm
      BinaryRegularRankFiveK28SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart29.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart29 hK.symm
      BinaryRegularRankFiveK29SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart30.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart30 hK.symm
      BinaryRegularRankFiveK30SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart31.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart31 hK.symm
      BinaryRegularRankFiveK31SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart32.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 6
      (by decide) chart32 hK.symm
      BinaryRegularRankFiveK32SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart33.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart33 hK.symm
      BinaryRegularRankFiveK33SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart34.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart34 hK.symm
      BinaryRegularRankFiveK34SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart35.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart35 hK.symm
      BinaryRegularRankFiveK35SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart36.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart36 hK.symm
      BinaryRegularRankFiveK36SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart37.space at hK
    exact F.regular_middle_kernel_unit_normalF_packet hU hrank hH 5
      (by decide) chart37 hK.symm
      BinaryRegularRankFiveK37SmallAxisCover.envelope N hnonab
  · change F.kernelSpace=chart38.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart38.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart39.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart39.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart40.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart40.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart41.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart41.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart42.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart42.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart43.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart43.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart44.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart44.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs
  · change F.kernelSpace=chart45.space at hK
    exact F.regular45_rank_five_unit_normalF_packet hU hrank hH
      (hK.trans kernel45_space) N hnonab
  · change F.kernelSpace=chart46.space at hK
    have hu := F.kernelSpace_card_mul_top
    rw [hK,chart46.card,ht] at hu
    norm_num at hu
    have hs := RDTNormalFSmallSixteenOrder.all_nonabelian_quotients hU
      (by simpa only [Nat.card_fin] using F.card_points)
      (by omega : Nat.card U ≤ 128) hrank N hnonab
    simpa only [one_mul] using normalF_packet_coefficient_mono
      1 (5/4) 8 4 (by norm_num) hs

end SymmetricSubgroupAsymptotics.BinaryPairFrame
