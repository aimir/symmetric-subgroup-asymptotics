import SymmetricSubgroupAsymptotics.BinaryPairRegularThreeHeadSectors
import SymmetricSubgroupAsymptotics.BinaryPairRegular46SourceJoint
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel46
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairRankAdditiveKernelNormalPacket
import SymmetricSubgroupAsymptotics.BinaryPairRankNineOrderBudgetNormalF
import SymmetricSubgroupAsymptotics.BinaryPairAugmentationSmallOrderNormalF
import SymmetricSubgroupAsymptotics.BinaryPairRegularAugmentationPreimage
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank

/-! Complete actual regular46 head-three sector. The small kernel range
is paid by the proved whole-source order budget. Above it, the SAME kernel
is the literal augmentation, so its small normals use the actual interval
packet and the remaining normals use the source/quotient joint bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance regular46RankNineNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem regular46_rank_nine_derived_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hthree : MarkedC4.normalGen F.top.ker=3) (hsix : MarkedC4.genRank F.top.range=6)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hJ : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 46).2.space)
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
  have hbound (A : Subgroup U) [A.Normal] (hA : A≤F.top.ker) : MarkedC4.normalGen A≤4 := by
    rw [F.axisNatural_normalGen A hA hU]
    exact E.naturalModuleHead_le_of_literal_pair_layer_bound
      BinaryRegularEightNaturalRegistry.H hH _ hJ 4
      BinaryPairLayerHead8T3Kernel46.pair_bound (F.axisNaturalSubrepresentation A)
  have hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range := by omega
  have hJdim : Module.finrank (ZMod 2) E.kernelSpace=4 := by
    rw [hJ]
    exact (BinaryRegularEightNaturalRegistry.charts 46).2.finrank
  have hcardH : Nat.card F.top.range=128 := by
    have hk : Nat.card E.kernelSpace=16 := by
      rw [hJ,(BinaryRegularEightNaturalRegistry.charts 46).2.card]
      rfl
    have ht : Nat.card E.top.range=8 := by rw [hH,BinaryMenuCayley8T3.exact_card]
    have hh := E.kernelSpace_card_mul_top
    rw [hk,ht] at hh
    omega
  have hnon : ¬∀ t : F.top.range,t^2=1 := by
    intro hh
    have he := ElementaryBinaryTransitiveNormalRank.card_eq_degree
      (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hh) (0 : Fin 16)
    rw [hcardH,Nat.card_fin] at he
    omega
  by_cases hsmallK : Module.finrank (ZMod 2) F.kernelSpace≤12
  · exact F.rank_nine_pair_dimension_order_budget_all_normal_unit hU hrank 12 7 hsmallK
      (by rw [hcardH];norm_num) (by decide) (by decide) hnon N hnonab
  obtain ⟨hLow,hSum⟩ := E.regular46_head_three_large_dimension_layers hTop hH hJ W hhead (by
    rw [hWspace]
    omega)
  have hAug := regular45_full_lower_kernel_eq_augmentation F E hSum hLow
  by_cases hsmallN : Nat.card N≤8
  · exact F.augmentation_small_order_normalF_packet E hU hAug (by omega) N hsmallN
  have hsourcejoint : Nat.card (commutator F.top.range)*
      Nat.card (Subgroup.center F.top.range)≤2^2 :=
    E.regular46_rank_six_source_joint_le_four hTop (by omega) hH hJ
  have hD : Nat.card (commutator F.top.range)≤4 := by
    have hp : 0<Nat.card (Subgroup.center F.top.range) := Nat.card_pos
    norm_num at hsourcejoint
    nlinarith
  have hquotjoint (M : Subgroup F.top.range) [M.Normal] :
      Nat.card (commutator (F.top.range ⧸ M))*
        Nat.card (Subgroup.center (F.top.range ⧸ M))≤2^6 :=
    E.sixteen_rank_six_small_derived_all_quotient_joint_le_sixty_four hTop (by omega) hD M
  by_cases hN : N≤F.top.ker
  · have hNcard : 16≤Nat.card N := by
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
    have hKcard : Nat.card F.kernelSpace≤2^15 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
      rw [Nat.card_zmod,hKdim] at hh
      exact hh.le
    have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^11 :=
      F.large_kernel_normal_image_card_le N hN 16 (2^15) (2^11) hNcard hKcard (by norm_num)
    exact F.rank_nine_rank_additive_kernel_normalF_packet hU hrank hadd 4 11 2 hbound
      hsourcejoint (by omega) N hN hND himage hnonab
  · have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^8 := by
      simpa using F.moving_normal_kernel_image_card_le_half hU (0 : Fin 16) N hN
    exact F.rank_nine_rank_additive_joint_normalF_packet hU hrank hadd 4 8 6 hbound
      hquotjoint (by omega) N hND himage hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
