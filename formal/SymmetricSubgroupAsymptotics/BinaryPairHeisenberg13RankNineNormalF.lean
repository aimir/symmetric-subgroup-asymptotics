import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergThreeHeadDimension
import SymmetricSubgroupAsymptotics.BinaryPairInnerThreeAxisBounds
import SymmetricSubgroupAsymptotics.BinaryPairRankAdditiveKernelNormalPacket
import SymmetricSubgroupAsymptotics.BinarySixteenHeadThreeTopJoint
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard

/-! Complete SAME-derived-denominator packet for the actual inner
Heisenberg13 sector. Its uniform subaxis capacity is three, its outer
kernel has dimension at most eleven, and its actual source top has joint
derived-times-centre at most32. No proper-F or offset classification is
needed in this entire sector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance heisenberg13RankNineNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem heisenberg13_rank_nine_derived_normalF_packet
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U=9)
    (hthree : MarkedC4.normalGen F.top.ker=3) (hsix : MarkedC4.genRank F.top.range=6)
    (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H)
    (hJ : E.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 13).2.space)
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
  have hbound (A : Subgroup U) [A.Normal] (hA : A≤F.top.ker) : MarkedC4.normalGen A≤3 :=
    F.normalGen_le_three_of_inner_heisenberg13 E hU hH hJ A hA
  have hadd : MarkedC4.genRank U=
      MarkedC4.normalGen F.top.ker+MarkedC4.genRank F.top.range := by omega
  have hquotjoint (M : Subgroup F.top.range) [M.Normal] :
      Nat.card (commutator (F.top.range ⧸ M))*
        Nat.card (Subgroup.center (F.top.range ⧸ M))≤2^8 :=
    E.sixteen_rank_six_head_three_all_quotient_joint_le_256 hTop (by omega) W hhead M
  by_cases hN : N≤F.top.ker
  · have hJdim : Module.finrank (ZMod 2) E.kernelSpace=5 := by
      rw [hJ]
      exact (BinaryHeisenbergEightNaturalHeads.charts 13).2.finrank
    have hd := E.heisenberg_head_three_dimension_add_kernel_le_sixteen hTop hH W hhead
    have hWspace : W.toSubmodule=F.kernelSpace := F.original_ambientAxis_kernel
    rw [hWspace,hJdim] at hd
    have hKcard : Nat.card F.kernelSpace≤2^11 := by
      have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace)
      rw [Nat.card_zmod] at he
      rw [he]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^11 :=
      F.large_kernel_normal_image_card_le N hN 1 (2^11) (2^11) (by
        have hp : 0<Nat.card N := Nat.card_pos
        omega) hKcard (by simp)
    have hD := E.sixteen_rank_six_head_three_derived_card_le_sixteen hTop (by omega) W hhead
    have hZ := E.original_center_le_two_of_large_kernel hTop (by omega)
    have hsourcejoint : Nat.card (commutator F.top.range)*
        Nat.card (Subgroup.center F.top.range)≤2^5 :=
      (Nat.mul_le_mul hD hZ).trans (by norm_num)
    exact F.rank_nine_rank_additive_kernel_normalF_packet hU hrank hadd 3 11 5 hbound
      hsourcejoint (by omega) N hN hND himage hnonab
  · have himage : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^8 := by
      simpa using F.moving_normal_kernel_image_card_le_half hU (0 : Fin 16) N hN
    exact F.rank_nine_rank_additive_joint_normalF_packet hU hrank hadd 3 8 8 hbound
      hquotjoint (by omega) N hND himage hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
