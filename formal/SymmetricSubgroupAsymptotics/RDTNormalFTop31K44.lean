import SymmetricSubgroupAsymptotics.BinaryEightTop31K44ZeroCapacity
import SymmetricSubgroupAsymptotics.BinaryEightTop31GroupBounds
import SymmetricSubgroupAsymptotics.BinaryPairCoarseNormalQuotientCenter
import SymmetricSubgroupAsymptotics.BinaryPairSharedJointAxisCards
import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! All original normal quotients in the small31/K44 family. One
zero-axis coordinate bound supplements generic source/derived cardinal
estimates. No original normal or source-row census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryRegularEightNaturalRegistry (chart0 chart44)
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem top31_kernel44_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : F.kernelSpace = chart44.space)
    (N : Subgroup U) [N.Normal] (hNderived : N ≤ commutator U)
    (hAbQ : Nat.card (Abelianization (U ⧸ N)) ≤ 32)
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let e : BinaryEightTop31CoordinateAction.H ≃* F.top.range := (MulEquiv.subgroupCongr hH).symm
  have he : ∀ r v, BinaryEightTop31CoordinateAction.rho r v =
      F.coordinateTopAction (e r) v := fun _ _ => rfl
  have hkcard : Nat.card F.kernelSpace = 8 := by rw [hK,chart44.card]; norm_num
  have hu : Nat.card U = 512 := by
    have ht : Nat.card F.top.range = 64 :=
      (Nat.card_congr e.symm.toEquiv).trans BinaryMenuCayley8T31.exact_card
    have hh := F.kernelSpace_card_mul_top
    rw [hkcard,ht] at hh
    omega
  have habU : 32 ≤ Nat.card (Abelianization U) := by
    have hp := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
    norm_num at hp
    exact hp
  have hdU : Nat.card (commutator U) ≤ 16 := by
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
    rw [hu] at hc
    nlinarith
  have hdN : Nat.card N * Nat.card (commutator (U ⧸ N)) ≤ 16 := by
    have hc := quotient_derived_card_mul_intersection N
    rw [inf_eq_left.mpr hNderived] at hc
    exact hc.le.trans hdU
  have hn : 0 < Nat.card N := Nat.card_pos
  have hd : Nat.card (commutator (U ⧸ N)) ≤ 16 := by nlinarith
  have hzTop : Nat.card (Subgroup.center F.top.range) ≤ 2 := by
    have hc := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
    rw [← hc]
    exact BinaryEightTop31GroupBounds.center_card_le_two
  have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 16 := by
    by_cases hN : N ≤ F.top.ker
    · have hh := (F.kernel_normal_center_card_mul_le_kernel_mul_top_center N hN).trans
        (Nat.mul_le_mul (le_of_eq hkcard) hzTop)
      nlinarith
    · by_cases hbig : 2 ≤ Nat.card (F.ambientAxis N)
      · have hh := two_mul_inf_card_le_of_not_le F.top.ker N hN
        rw [← F.axis_card_eq_kernel_intersection N] at hh
        have hdsmall : Nat.card (commutator (U ⧸ N)) ≤ 4 := by nlinarith
        exact CentralIndexFourDerivedBound.center_card_le_sixteen_of_small_derived
          (hU.to_quotient N) hdsmall hAbQ hnonab
      · have hc : Nat.card (F.ambientAxis N) =
            2^Module.finrank (ZMod 2) (F.ambientAxis N) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.ambientAxis N))
        have hzero : Module.finrank (ZMod 2) (F.ambientAxis N) = 0 := by
          by_contra h
          have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
            (show 1 ≤ Module.finrank (ZMod 2) (F.ambientAxis N) by omega)
          norm_num at hp
          omega
        have hbot : F.ambientAxis N = ⊥ := Submodule.finrank_eq_zero.mp hzero
        have haxis : F.ambientAxis N = chart0.space := hbot.trans
          (Submodule.finrank_eq_zero.mp chart0.finrank).symm
        have hh := F.arbitrary_normal_center_card_mul_le N
        rw [F.shared_fixed_axis_card BinaryEightTop31CoordinateAction.rho e he N chart44.space hK.symm,
          F.shared_top_axis_card BinaryEightTop31CoordinateAction.rho e he N chart44.space hK.symm,haxis] at hh
        have hp := hh.trans BinaryEightTop31K44ZeroCapacity.coordinate_capacity
        have hNC := two_mul_inf_card_le_of_not_le F.top.ker N hN
        have ha : 0 < Nat.card (F.top.ker ⊓ N : Subgroup U) := Nat.card_pos
        nlinarith
  have hp := normalF_unit_packet_of_actual_product_bound (⊤ : Subgroup (U ⧸ N)) 8 4
    (by simpa only [MarkedC4.RDTNormalFInterface.targetCommutator,
      MarkedC4.RDTNormalFInterface.targetCentralizer,Subgroup.coe_top,
      Subgroup.centralizer_univ] using (Nat.mul_le_mul hd hz).trans (by norm_num : 16*16 ≤ 2^8))
    (by simpa only [MarkedC4.RDTNormalFInterface.targetCentralizer,Subgroup.coe_top,
      Subgroup.centralizer_univ] using hz)
  exact ⟨⊤,inferInstance,hp.1,hp.2⟩
end SymmetricSubgroupAsymptotics.BinaryPairFrame
