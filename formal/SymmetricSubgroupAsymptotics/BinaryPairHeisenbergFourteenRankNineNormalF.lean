import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenHighLayers
import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenThirteenNormalF
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairRankAdditiveKernelNormalPacket
import SymmetricSubgroupAsymptotics.BinarySixteenSmallDerivedJoint

/-! Complete SAME-derived-denominator packet in the actual inner
Heisenberg14 head-three sector. Every high-dimensional kernel has the
proved original thirteen-dimensional layer geometry; its small normals
use the actual pure-flip interval packet. Other cases use joint bounds
with the SAME denominator and the actual correlated kernel image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance heisenbergFourteenRankNineNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem heisenberg14_rank_nine_derived_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hthree : MarkedC4.normalGen F.top.ker=3) (hsix : MarkedC4.genRank F.top.range=6)
    (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H)
    (hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
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
      BinaryHeisenbergEightNaturalHeads.H hH _ hJ 4
      BinaryPairLayerHead8T22Kernel14.pair_bound (F.axisNaturalSubrepresentation A)
  have hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range := by omega
  have hcardH : Nat.card F.top.range≤256 := by
    have hk : Nat.card E.kernelSpace=8 := by
      rw [hJ,(BinaryHeisenbergEightNaturalHeads.charts 14).2.card]
      rfl
    have ht : Nat.card E.top.range=32 := by rw [hH,BinaryMenuCayley8T22.exact_card]
    have hh := E.kernelSpace_card_mul_top
    rw [hk,ht] at hh
    omega
  have hD : Nat.card (commutator F.top.range)≤4 :=
    sixteen_rank_six_order_le_256_derived_card_le_four hTop (by omega) hcardH
  have hsourcejoint : Nat.card (commutator F.top.range)*
      Nat.card (Subgroup.center F.top.range)≤2^4 := by
    simpa using E.sixteen_rank_six_small_order_heisenberg_top_joint_le_sixteen
      hTop (by omega) hcardH hH
  have hquotjoint (M : Subgroup F.top.range) [M.Normal] :
      Nat.card (commutator (F.top.range ⧸ M))*
        Nat.card (Subgroup.center (F.top.range ⧸ M))≤2^6 := by
    simpa using E.sixteen_rank_six_small_derived_all_quotient_joint_le_sixty_four
      hTop (by omega) hD M
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
    F.rank_nine_rank_additive_kernel_normalF_packet hU hrank hadd 4 11 4 hbound
      hsourcejoint (by omega) N hN hND himage hnonab
  by_cases hN : N≤F.top.ker
  · by_cases hsmallK : Module.finrank (ZMod 2) F.kernelSpace≤11
    · apply hfinish hN
      exact F.large_kernel_normal_image_card_le N hN 1 (2^11) (2^11) (by
        have hp : 0<Nat.card N := Nat.card_pos
        omega) (hcardOfDim 11 hsmallK) (by simp)
    obtain ⟨hSum,hLow⟩ := E.heisenberg14_large_head_three_original_layers hH hJ W (by
      rw [hWspace]
      omega) hhead
    by_cases hsmallN : Nat.card N≤2
    · exact F.heisenberg14_thirteen_small_normalF_packet E hU hH hJ hSum hLow N hsmallN
    have hNcard : 4≤Nat.card N := by
      obtain ⟨k,hk⟩ := (hU.to_subgroup N).exists_card_eq
      have htwo : 2≤k := by
        by_contra hh
        have hb := Nat.pow_le_pow_right (by decide : 0<2) (show k≤1 from by omega)
        rw [←hk] at hb
        norm_num at hb
        omega
      rw [hk]
      exact Nat.pow_le_pow_right (by decide : 0<2) htwo
    have hKdim : Module.finrank (ZMod 2) F.kernelSpace=13 := by
      have hd := E.pairModuleLayers_finrank W
      rw [hWspace,hSum,hLow,BinaryRegularEightNaturalRegistry.chart33.finrank] at hd
      have hLdim : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin 8 → ZMod 2))=8 := by simp
      rw [hLdim] at hd
      omega
    apply hfinish hN
    exact F.large_kernel_normal_image_card_le N hN 4 (2^13) (2^11) hNcard
      (hcardOfDim 13 hKdim.le) (by norm_num)
  · have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^8 := by
      simpa using F.moving_normal_kernel_image_card_le_half hU (0 : Fin 16) N hN
    exact F.rank_nine_rank_additive_joint_normalF_packet hU hrank hadd 4 8 6 hbound
      hquotjoint (by omega) N hND himage hnonab
end SymmetricSubgroupAsymptotics.BinaryPairFrame
