import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.NormalFUnitCostFromJointBounds
import SymmetricSubgroupAsymptotics.BinaryPairSharedJointAxisCards
import SymmetricSubgroupAsymptotics.DerivedQuotientSubgroupBound

/-! The unit joint-axis installer at ONE actual original normal axis.
This permits a proper-normal-F construction on exceptional axes without
requiring a false whole-quotient envelope on those axes. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate

theorem heisenberg_unit_normalF_of_one_doubled_axis_envelope
    (hU : IsPGroup 2 U)
    (hH : F.top.range = H)
    (K R : Submodule (ZMod 2) V) (hK : K = F.kernelSpace) (hRK : R ≤ K)
    (hRD : F.coordinateSubgroup R ≤ commutator U)
    (originalDerived : ℕ) (hD : Nat.card (commutator U) ≤ 2 * originalDerived)
    (hDsmall : originalDerived ≤ 2 * Nat.card R)
    (hsource : Nat.card U ≤ 128 * Nat.card R)
    (N : Subgroup U) [N.Normal]
    (henvelope : JointAxisEnvelope K R (F.ambientAxis N) originalDerived)
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let e : H ≃* F.top.range := (MulEquiv.subgroupCongr hH).symm
  have he : ∀ g v, rho g v = F.coordinateTopAction (e g) v := fun _ _ => rfl
  let A := F.sharedOriginalAxis rho e he N
  have hAK : A.toSubmodule ≤ K := (F.ambientAxis_le_kernelSpace N).trans_eq hK.symm
  obtain ⟨d, z, hd, hcenter, hcost, hz, hnonkernel⟩ := henvelope
  have hAR : A.toSubmodule ⊓ R ≤ F.kernelSpace := inf_le_left.trans (hAK.trans_eq hK)
  have hBN : F.coordinateSubgroup (A.toSubmodule ⊓ R) ≤ N := by
    apply (F.coordinateSubgroup_mono (show A.toSubmodule ⊓ R ≤ F.ambientAxis N from inf_le_left)).trans
    rw [F.coordinateSubgroup_ambientAxis]
    exact inf_le_right
  have hBD : F.coordinateSubgroup (A.toSubmodule ⊓ R) ≤ commutator U :=
    (F.coordinateSubgroup_mono inf_le_right).trans hRD
  have hdquot : Nat.card (commutator (U ⧸ N)) ≤ 2 ^ (d + 1) := by
    apply quotient_derived_card_le_of_subgroup N
      (F.coordinateSubgroup (A.toSubmodule ⊓ R)) hBN hBD
    rw [F.coordinateSubgroup_card _ hAR]
    calc
      Nat.card (commutator U) ≤ 2 * originalDerived := hD
      _ ≤ 2 * (Nat.card (A.toSubmodule ⊓ R : Submodule (ZMod 2) V) * 2 ^ d) :=
        Nat.mul_le_mul_left 2 hd
      _ = Nat.card (A.toSubmodule ⊓ R : Submodule (ZMod 2) V) * 2 ^ (d + 1) := by
        rw [pow_succ]
        ac_rfl
  by_cases hN : N ≤ F.top.ker
  · have hc : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2 ^ z := by
      apply F.center_card_le_of_joint_axis N z
      rw [if_pos hN, if_pos hN, one_mul,
        F.shared_fixed_axis_card rho e he N K hK,
        F.shared_central_top_axis_card rho e he N K hK]
      exact hcenter
    exact unit_packet_of_doubled_joint_card_bounds (hU.to_quotient N) hnonab
      d z hdquot hc hcost hz
  · rcases hnonkernel with hRA | ⟨zn, hzn, hzncost, hznle⟩
    · have hRleN : F.coordinateSubgroup R ≤ N := by
        apply (F.coordinateSubgroup_mono hRA).trans
        change F.coordinateSubgroup (F.ambientAxis N) ≤ N
        rw [F.coordinateSubgroup_ambientAxis]
        exact inf_le_right
      have hRcard := F.coordinateSubgroup_card R (hRK.trans_eq hK)
      have hcardA : Nat.card R ≤ Nat.card (F.ambientAxis N) :=
        Nat.card_le_card_of_injective (Submodule.inclusion hRA)
          (Submodule.inclusion_injective hRA)
      have hcardN := two_mul_inf_card_le_of_not_le F.top.ker N hN
      rw [← F.axis_card_eq_kernel_intersection N] at hcardN
      have hquot := N.card_eq_card_quotient_mul_card_subgroup
      have hp : 0 < Nat.card R := Nat.card_pos
      have hq : Nat.card (U ⧸ N) ≤ 64 := by nlinarith
      have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
      have hc := (Subgroup.center (U ⧸ N)).card_mul_index
      have hz16 : Nat.card (Subgroup.center (U ⧸ N)) ≤ 16 := by nlinarith
      have hd4 : Nat.card (commutator (U ⧸ N)) ≤ 4 := by
        apply quotient_derived_card_le_of_subgroup N (F.coordinateSubgroup R) hRleN hRD
        rw [hRcard]
        calc
          Nat.card (commutator U) ≤ 2 * originalDerived := hD
          _ ≤ 2 * (2 * Nat.card R) := Nat.mul_le_mul_left 2 hDsmall
          _ = Nat.card R * 4 := by ac_rfl
      exact unit_packet_of_doubled_joint_card_bounds (hU.to_quotient N) hnonab
        1 4 (by simpa using hd4) (by simpa using hz16) (by decide) (by decide)
    · have hc : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2 ^ zn := by
        apply F.center_card_le_of_joint_axis N zn
        rw [if_neg hN, if_neg hN,
          F.shared_fixed_axis_card rho e he N K hK,
          F.shared_top_axis_card rho e he N K hK]
        exact hzn
      exact unit_packet_of_doubled_joint_card_bounds (hU.to_quotient N) hnonab
        d zn hdquot hc hzncost hznle

end SymmetricSubgroupAsymptotics.BinaryPairFrame
