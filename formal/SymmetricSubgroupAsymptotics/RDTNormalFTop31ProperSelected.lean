import SymmetricSubgroupAsymptotics.BinaryPairAffineProperFPacket
import SymmetricSubgroupAsymptotics.BinaryPairAugmentationDerivedZeroLifts
import SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFCapacities
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds

/-! Two actual proper-F packets for the original31 augmentation source.
Only the zero and constant-line kernel denominators need these cuts.
Their selected central flip is lifted from the ACTUAL affine cocycle;
the extension and all other original offsets need not split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryRegularEightNaturalRegistry (chart0 chart9 chart23 chart26 chart37 chart45)
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

private theorem top31_selected_proper_unit
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : F.kernelSpace = chart45.space)
    (B C A : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hB : B ≤ chart45.space) (hCB : C ≤ B)
    (hCstable : ∀ r v, v ∈ C → BinaryEightTop31CoordinateAction.rho r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → BinaryEightTop31CoordinateAction.rho r v-v ∈ C)
    (hzdisp : ∀ v, BinaryEightTop31CoordinateAction.rho BinaryEightTop31ProperFLinear.z v-v ∈ C)
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker)
    (haxis : F.ambientAxis N = A) (hAC : A ≤ C)
    (hcomm : Nat.card C ≤ Nat.card N * 16)
    (hcapacity :
      Nat.card {v : BinaryEightTop31CoordinateAction.V // v ∈ chart45.space ∧
        BinaryEightTop31CoordinateAction.rho BinaryEightTop31ProperFLinear.z v-v ∈ A} *
      Nat.card {t : BinaryEightTop31CoordinateAction.H // ∀ v, v ∈ B →
        BinaryEightTop31CoordinateAction.rho t v-v ∈ A} ≤ Nat.card N * 16) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let e : BinaryEightTop31CoordinateAction.H ≃* F.top.range :=
    (MulEquiv.subgroupCongr hH).symm
  have he : ∀ r v, BinaryEightTop31CoordinateAction.rho r v =
      F.coordinateTopAction (e r) v := fun _ _ => rfl
  let z := e BinaryEightTop31ProperFLinear.z
  have hz : z ∈ Subgroup.center F.top.range := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨r,rfl⟩ := e.surjective t
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_center_iff.mp BinaryEightTop31ProperFLinear.z_central r)
  have hderived : z ∈ commutator F.top.range := by
    have hzmap : z ∈ (commutator BinaryEightTop31CoordinateAction.H).map e.toMonoidHom :=
      ⟨_,BinaryEightTop31ProperFLinear.z_derived,rfl⟩
    have hm : (commutator BinaryEightTop31CoordinateAction.H).map e.toMonoidHom =
        commutator F.top.range := by
      rw [commutator_def,Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      rfl
    exact hm ▸ hzmap
  have hzero := F.affineClass_eq_zero_of_derived_top
    (F.affineQuotient_trivial_of_augmentation_kernel hK) z hderived
  apply F.affine_properF_unit_packet B C z
    (by rw [hK]; exact hB) (by rw [hK]; exact hCB.trans hB) hCB hz hzero
  · intro r v hv
    obtain ⟨t,rfl⟩ := e.surjective r
    exact hCstable t v hv
  · intro r v hv
    obtain ⟨t,rfl⟩ := e.surjective r
    exact hBdisp t v hv
  · exact hzdisp
  · exact hN
  · rw [haxis]
    exact hAC
  · exact hcomm
  · have ht : Nat.card {t : F.top.range // ∀ v, v ∈ B →
          F.coordinateTopAction t v-v ∈ A} =
        Nat.card {t : BinaryEightTop31CoordinateAction.H // ∀ v, v ∈ B →
          BinaryEightTop31CoordinateAction.rho t v-v ∈ A} := by
      symm
      apply Nat.card_congr
      refine e.toEquiv.subtypeEquiv ?_
      intro t
      simp only [he]
      rfl
    rw [hK,haxis,ht]
    exact hcapacity

/-- Original source packet, since a kernel denominator with zero axis is
trivial. No quotient or top image is silently substituted. -/
theorem top31_kernel45_zero_axis_unit
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : F.kernelSpace = chart45.space) (N : Subgroup U) [N.Normal]
    (hN : N ≤ F.top.ker) (haxis : F.ambientAxis N = chart0.space) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have hn : Nat.card N = 1 := by
    have hc := F.axis_card_eq_kernel_intersection N
    rw [inf_eq_right.mpr hN,haxis,chart0.card] at hc
    simpa using hc.symm
  apply F.top31_selected_proper_unit hH hK chart37.space chart9.space chart0.space
    (chart37.le_of_basis_mem _ (by decide +kernel))
    BinaryEightTop31ProperFLinear.envelope_le_layer
    (fun r v hv => BinaryEightTop31ProperFLinear.envelope.apply_mem_toSubmodule r hv)
    BinaryEightTop31ProperFLinear.layer_displacement
    BinaryEightTop31ProperFLinear.flip_displacement N hN haxis
  · exact chart0.le_of_basis_mem _ (by intro j; exact Fin.elim0 j)
  · rw [chart9.card,hn]
    norm_num
  · exact BinaryEightTop31ProperFCapacities.zero_coordinate_capacity.trans (by norm_num [hn])

/-- The only second proper-F case is the exact original constant axis. -/
theorem top31_kernel45_constant_axis_unit
    (hH : F.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : F.kernelSpace = chart45.space) (N : Subgroup U) [N.Normal]
    (hN : N ≤ F.top.ker) (haxis : F.ambientAxis N = chart23.space) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have hn : Nat.card N = 2 := by
    have hc := F.axis_card_eq_kernel_intersection N
    rw [inf_eq_right.mpr hN,haxis,chart23.card] at hc
    norm_num at hc
    exact hc.symm
  apply F.top31_selected_proper_unit hH hK chart26.space chart37.space chart23.space
    BinaryEightTop31ProperF26Linear.layer_le_kernel
    BinaryEightTop31ProperF26Linear.envelope_le_layer
    (fun r v hv => BinaryEightTop31ProperF26Linear.envelope.apply_mem_toSubmodule r hv)
    BinaryEightTop31ProperF26Linear.layer_displacement
    BinaryEightTop31ProperF26Linear.flip_displacement N hN haxis
  · exact chart23.le_of_basis_mem _ (by decide +kernel)
  · rw [chart37.card,hn]
    norm_num
  · exact BinaryEightTop31ProperFCapacities.constant_coordinate_capacity.trans (by norm_num [hn])
end SymmetricSubgroupAsymptotics.BinaryPairFrame
