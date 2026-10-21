import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel
import SymmetricSubgroupAsymptotics.BinaryEightTop29SmallAxes
import SymmetricSubgroupAsymptotics.BinaryEightTop29GroupBounds
import SymmetricSubgroupAsymptotics.BinaryEightTop29K30AxisZeroCapacity
import SymmetricSubgroupAsymptotics.BinaryEightTop29K30Axis22Pilot
import SymmetricSubgroupAsymptotics.BinaryEightTop29K30Axis23Capacity
import SymmetricSubgroupAsymptotics.BinaryPairCoarseNormalQuotientCenter
import SymmetricSubgroupAsymptotics.BinaryPairSharedJointAxisCards
import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! Every SAME original normal quotient in the selected actual8T29/K30
family. Large axes use generic actual order bounds. Only the three small
axes use finite coordinate envelopes. No lift offset or split extension
is selected; the exact excess-one adapter supplies the derived-denominator
and full quotient-abelianization hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryRegularEightNaturalRegistry (chart0 chart22 chart23 chart30)

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

/-- Algebraic input from the original rank-preserving excess-one quotient
is explicit here; no new retained hypothesis is added by this installer. -/
theorem top29_kernel30_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = BinaryEightTop29CoordinateAction.H)
    (hK : F.kernelSpace = chart30.space)
    (N : Subgroup U) [N.Normal] (hNderived : N ≤ commutator U)
    (hAbQ : Nat.card (Abelianization (U ⧸ N)) ≤ 32)
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let e : BinaryEightTop29CoordinateAction.H ≃* F.top.range :=
    (MulEquiv.subgroupCongr hH).symm
  have he : ∀ g v, BinaryEightTop29CoordinateAction.rho g v =
      F.coordinateTopAction (e g) v := fun _ _ => rfl
  have hkcard : Nat.card F.kernelSpace = 32 := by rw [hK,chart30.card]; norm_num
  have htopcard : Nat.card F.top.range = 64 :=
    (Nat.card_congr e.symm.toEquiv).trans BinaryMenuCayley8T29.exact_card
  have hu : Nat.card U = 2048 := by
    have hh := F.kernelSpace_card_mul_top
    rw [hkcard,htopcard] at hh
    omega
  have habU : 32 ≤ Nat.card (Abelianization U) := by
    have hp := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
    norm_num at hp
    exact hp
  have hdU : Nat.card (commutator U) ≤ 64 := by
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
    rw [hu] at hc
    nlinarith
  have hdN : Nat.card N * Nat.card (commutator (U ⧸ N)) ≤ 64 := by
    have hc := quotient_derived_card_mul_intersection N
    rw [inf_eq_left.mpr hNderived] at hc
    exact hc.le.trans hdU
  have haN : Nat.card (F.ambientAxis N) ≤ Nat.card N := by
    rw [F.axis_card_eq_kernel_intersection N]
    exact Subgroup.card_le_of_le inf_le_right
  have hAD : Nat.card (F.ambientAxis N) * Nat.card (commutator (U ⧸ N)) ≤ 64 :=
    (Nat.mul_le_mul_right _ haN).trans hdN
  have hzTop : Nat.card (Subgroup.center F.top.range) ≤ 2 := by
    have hc := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
    rw [← hc]
    exact BinaryEightTop29GroupBounds.center_card_le_two
  have finish (hd hz : ℕ)
      (hderived : Nat.card (commutator (U ⧸ N)) ≤ hd)
      (hcenter : Nat.card (Subgroup.center (U ⧸ N)) ≤ hz)
      (hprod : hd * hz ≤ 256) (hzc : hz ≤ 16) :
      ∃ W : Subgroup (U ⧸ N), W.Normal ∧
        MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
          MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
    have hp := normalF_unit_packet_of_actual_product_bound (⊤ : Subgroup (U ⧸ N)) 8 4
      (by simpa only [MarkedC4.RDTNormalFInterface.targetCommutator,
        MarkedC4.RDTNormalFInterface.targetCentralizer,Subgroup.coe_top,
        Subgroup.centralizer_univ] using (Nat.mul_le_mul hderived hcenter).trans hprod)
      (by simpa only [MarkedC4.RDTNormalFInterface.targetCentralizer,
        Subgroup.coe_top,Subgroup.centralizer_univ] using hcenter.trans hzc)
    exact ⟨⊤,inferInstance,hp.1,hp.2⟩
  have small (hsmall : Nat.card (F.ambientAxis N) < 8) :
      ∃ W : Subgroup (U ⧸ N), W.Normal ∧
        MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
          MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
    let A := F.literalTopAxis BinaryEightTop29CoordinateAction.H hH N
    have hAs : A.toSubmodule = F.ambientAxis N := F.literalTopAxis_space _ hH N
    rcases BinaryEightTop29SmallAxes.small_space A (by simpa only [hAs] using hsmall) with
      hzero | htwo | hone
    · have haxis : F.ambientAxis N = chart0.space := hAs.symm.trans hzero
      have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2^1 := by
        apply F.center_card_le_of_joint_axis N 1
        by_cases hN : N ≤ F.top.ker
        · rw [if_pos hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_central_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30AxisZeroCapacity.central_coordinate_capacity.trans (by rw [chart0.card]; norm_num [hN])
        · rw [if_neg hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30AxisZeroCapacity.coordinate_capacity.trans (by rw [chart0.card]; norm_num [hN])
      have hd : Nat.card (commutator (U ⧸ N)) ≤ 64 := by
        rw [haxis,chart0.card] at hAD
        norm_num at hAD
        omega
      exact finish 64 (2^1) hd hz (by norm_num) (by norm_num)
    · have haxis : F.ambientAxis N = chart22.space := hAs.symm.trans htwo
      have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2^4 := by
        apply F.center_card_le_of_joint_axis N 4
        by_cases hN : N ≤ F.top.ker
        · rw [if_pos hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_central_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30Axis22Pilot.central_coordinate_capacity.trans (by rw [chart22.card]; norm_num [hN])
        · rw [if_neg hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30Axis22Pilot.coordinate_capacity.trans (by rw [chart22.card]; norm_num [hN])
      have hd : Nat.card (commutator (U ⧸ N)) ≤ 16 := by
        rw [haxis,chart22.card] at hAD
        norm_num at hAD
        omega
      exact finish 16 (2^4) hd hz (by norm_num) (by norm_num)
    · have haxis : F.ambientAxis N = chart23.space := hAs.symm.trans hone
      have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2^2 := by
        apply F.center_card_le_of_joint_axis N 2
        by_cases hN : N ≤ F.top.ker
        · rw [if_pos hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_central_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30Axis23Capacity.central_coordinate_capacity.trans (by rw [chart23.card]; norm_num [hN])
        · rw [if_neg hN]
          rw [F.shared_fixed_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,
            F.shared_top_axis_card BinaryEightTop29CoordinateAction.rho e he N
            chart30.space hK.symm,haxis]
          exact BinaryEightTop29K30Axis23Capacity.coordinate_capacity.trans (by rw [chart23.card]; norm_num [hN])
      have hd : Nat.card (commutator (U ⧸ N)) ≤ 32 := by
        rw [haxis,chart23.card] at hAD
        norm_num at hAD
        omega
      exact finish 32 (2^2) hd hz (by norm_num) (by norm_num)
  by_cases hN : N ≤ F.top.ker
  · by_cases hbig : 4 ≤ Nat.card (F.ambientAxis N)
    · have hn : 4 ≤ Nat.card N := hbig.trans haN
      have hd : Nat.card (commutator (U ⧸ N)) ≤ 16 := by nlinarith
      have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 16 := by
        have hh := (F.kernel_normal_center_card_mul_le_kernel_mul_top_center N hN).trans
          (Nat.mul_le_mul (le_of_eq hkcard) hzTop)
        nlinarith
      exact finish 16 16 hd hz (by norm_num) le_rfl
    · exact small (by omega)
  · by_cases hbig : 8 ≤ Nat.card (F.ambientAxis N)
    · have hi := two_mul_inf_card_le_of_not_le F.top.ker N hN
      rw [← F.axis_card_eq_kernel_intersection N] at hi
      have hn : 16 ≤ Nat.card N := by omega
      have hd : Nat.card (commutator (U ⧸ N)) ≤ 4 := by nlinarith
      have hz := CentralIndexFourDerivedBound.center_card_le_sixteen_of_small_derived
        (hU.to_quotient N) hd hAbQ hnonab
      exact finish 4 16 hd hz (by norm_num) le_rfl
    · exact small (by omega)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
