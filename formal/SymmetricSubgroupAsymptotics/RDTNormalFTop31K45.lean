import SymmetricSubgroupAsymptotics.RDTNormalFTop31ProperSelected
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel
import SymmetricSubgroupAsymptotics.BinaryEightTop31K45AxisCoverage
import SymmetricSubgroupAsymptotics.BinaryPairSharedJointAxisCards
import SymmetricSubgroupAsymptotics.CentralIndexFourDerivedBound
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! Every SAME original normal quotient in the31 augmentation family.
Only zero/constant kernel denominators use selected proper normal images.
All other axes use joint Qtop factors; large outside normals use the
proved small-derived/abelianization bound. No split extension is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryRegularEightNaturalRegistry (chart45)
open BinaryEightTop31K45JointCounts
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem top31_kernel45_all_normal_unit
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : F.kernelSpace = chart45.space)
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
  have hu : Nat.card U = 8192 := by
    have hk : Nat.card F.kernelSpace = 128 := by rw [hK,chart45.card]; norm_num
    have ht : Nat.card F.top.range = 64 :=
      (Nat.card_congr e.symm.toEquiv).trans BinaryMenuCayley8T31.exact_card
    have hh := F.kernelSpace_card_mul_top
    rw [hk,ht] at hh
    omega
  have habU : 32 ≤ Nat.card (Abelianization U) := by
    have hp := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
    norm_num at hp
    exact hp
  have hdU : Nat.card (commutator U) ≤ 256 := by
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
    rw [hu] at hc
    nlinarith
  have hdN : Nat.card N * Nat.card (commutator (U ⧸ N)) ≤ 256 := by
    have hc := quotient_derived_card_mul_intersection N
    rw [inf_eq_left.mpr hNderived] at hc
    exact hc.le.trans hdU
  have hAD : Nat.card (F.ambientAxis N) * Nat.card (commutator (U ⧸ N)) ≤ 256 :=
    (Nat.mul_le_mul_right _ (by
      rw [F.axis_card_eq_kernel_intersection N]
      exact Subgroup.card_le_of_le inf_le_right)).trans hdN
  let A := F.literalTopAxis BinaryEightTop31CoordinateAction.H hH N
  have hAs : A.toSubmodule = F.ambientAxis N := F.literalTopAxis_space _ hH N
  obtain ⟨i,hi⟩ := BinaryEightTop31K45AxisCoverage.complete A (by
    rw [hAs,← hK]
    exact F.ambientAxis_le_kernelSpace N)
  have haxis : F.ambientAxis N = (axes i).2.space := hAs.symm.trans hi
  have hd : Nat.card (commutator (U ⧸ N)) ≤ 2^(derivedExponent i) := by
    have hp : 0 < Nat.card (F.ambientAxis N) := Nat.card_pos
    have hc := derived_arithmetic i
    rw [← haxis] at hc
    nlinarith
  have finish (d z : ℕ)
      (hderived : Nat.card (commutator (U ⧸ N)) ≤ d)
      (hcenter : Nat.card (Subgroup.center (U ⧸ N)) ≤ z)
      (hprod : d*z ≤ 256) (hzc : z ≤ 16) :
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
  by_cases hN : N ≤ F.top.ker
  · by_cases hzero : i = 0
    · subst i
      exact F.top31_kernel45_zero_axis_unit hH hK N hN haxis
    by_cases hone : i = 5
    · subst i
      exact F.top31_kernel45_constant_axis_unit hH hK N hN haxis
    have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2^(insideExponent i) := by
      apply F.center_card_le_of_joint_axis N (insideExponent i)
      simp only [if_pos hN,one_mul]
      rw [F.shared_fixed_axis_card BinaryEightTop31CoordinateAction.rho e he N chart45.space hK.symm,
        F.shared_central_top_axis_card BinaryEightTop31CoordinateAction.rho e he N chart45.space hK.symm,
        haxis]
      exact inside_capacity i
    exact finish _ _ hd hz (inside_cost i hzero hone).1 (inside_cost i hzero hone).2
  · by_cases hlarge : 5 ≤ (axes i).1
    · have hbig : 32 ≤ Nat.card (F.ambientAxis N) := by
        rw [haxis,(axes i).2.card]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hlarge
      have hNcard := two_mul_inf_card_le_of_not_le F.top.ker N hN
      rw [← F.axis_card_eq_kernel_intersection N] at hNcard
      have hdsmall : Nat.card (commutator (U ⧸ N)) ≤ 4 := by nlinarith
      have hz := CentralIndexFourDerivedBound.center_card_le_sixteen_of_small_derived (hU.to_quotient N) hdsmall hAbQ hnonab
      exact finish 4 16 hdsmall hz (by norm_num) (by norm_num)
    · have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2^(outsideExponent i) := by
        apply F.center_card_le_of_joint_axis N (outsideExponent i)
        simp only [if_neg hN]
        rw [F.shared_fixed_axis_card BinaryEightTop31CoordinateAction.rho e he N chart45.space hK.symm,
          F.shared_top_axis_card BinaryEightTop31CoordinateAction.rho e he N chart45.space hK.symm,haxis]
        exact outside_capacity i
      exact finish _ _ hd hz (outside_cost i (by omega)).1 (outside_cost i (by omega)).2
end SymmetricSubgroupAsymptotics.BinaryPairFrame
