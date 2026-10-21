import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter
import SymmetricSubgroupAsymptotics.DerivedQuotientExactCard
import SymmetricSubgroupAsymptotics.NormalKernelIntersectionCard
import SymmetricSubgroupAsymptotics.RDTNormalFSmallSixteenOrder

/-! Joint all-normal bounds use the SAME literal axis for the fixed-vector,
top-displacement and derived-intersection charges. No split lift is chosen. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

omit [Finite X] in
theorem axis_card_eq_kernel_intersection (N : Subgroup U) :
    Nat.card (F.ambientAxis N) = Nat.card (F.top.ker ⊓ N : Subgroup U) := by
  rw [← F.coordinateSubgroup_card (F.ambientAxis N) (F.ambientAxis_le_kernelSpace N),
    F.coordinateSubgroup_ambientAxis]

theorem derived_card_le_of_axis (N : Subgroup U) [N.Normal]
    (haxis : F.coordinateSubgroup (F.ambientAxis N) ≤ commutator U)
    (d : ℕ) (hd : Nat.card (commutator U) ≤ Nat.card (F.ambientAxis N) * 2 ^ d) :
    Nat.card (commutator (U ⧸ N)) ≤ 2 ^ d := by
  have hle : F.top.ker ⊓ N ≤ N ⊓ commutator U := by
    rw [← F.coordinateSubgroup_ambientAxis N]
    exact le_inf (by rw [F.coordinateSubgroup_ambientAxis]; exact inf_le_right) haxis
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  have he := quotient_derived_card_mul_intersection N
  rw [F.axis_card_eq_kernel_intersection N] at hd
  have hp : 0 < Nat.card (F.top.ker ⊓ N : Subgroup U) := Nat.card_pos
  nlinarith

theorem center_card_le_of_joint_axis (N : Subgroup U) [N.Normal] (z : ℕ)
    (hcapacity :
      (if N ≤ F.top.ker then
        Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
          ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} *
          Nat.card {t : F.top.range // t ∈ Subgroup.center F.top.range ∧
            ∀ v, v ∈ F.kernelSpace → F.coordinateTopAction t v - v ∈ F.ambientAxis N}
        else
        Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
          ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} *
          Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
            F.coordinateTopAction t v - v ∈ F.ambientAxis N}) ≤
      (if N ≤ F.top.ker then 1 else 2) * Nat.card (F.ambientAxis N) * 2 ^ z) :
    Nat.card (Subgroup.center (U ⧸ N)) ≤ 2 ^ z := by
  by_cases hN : N ≤ F.top.ker
  · rw [if_pos hN, if_pos hN, one_mul] at hcapacity
    have hc := (F.kernel_normal_center_card_mul_le N hN).trans hcapacity
    have he : Nat.card (F.ambientAxis N) = Nat.card N := by
      rw [F.axis_card_eq_kernel_intersection N, inf_eq_right.mpr hN]
    rw [he] at hc
    have hp : 0 < Nat.card N := Nat.card_pos
    nlinarith
  · rw [if_neg hN, if_neg hN] at hcapacity
    have hc := (F.arbitrary_normal_center_card_mul_le N).trans hcapacity
    have hi := two_mul_inf_card_le_of_not_le F.top.ker N hN
    rw [← F.axis_card_eq_kernel_intersection N] at hi
    have hp : 0 < Nat.card (F.ambientAxis N) := Nat.card_pos
    nlinarith

theorem top_packet_of_joint_card_bounds
    {Q : Type} [Group Q] [Finite Q] (d z : ℕ)
    (hd : Nat.card (commutator Q) ≤ 2 ^ d)
    (hz : Nat.card (Subgroup.center Q) ≤ 2 ^ z)
    (hcost : 4 * d + 5 * z ≤ 32) (hzcost : z ≤ 4) :
    ∃ V : Subgroup Q, V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : MarkedC4.ActualNormalFMarkedPeel.commutatorLog (⊤ : Subgroup Q) ≤ d := by
    exact hlog _ d Nat.card_pos hd
  have hzlog : MarkedC4.ActualNormalFMarkedPeel.centralLog (⊤ : Subgroup Q) ≤ z := by
    simpa only [MarkedC4.ActualNormalFMarkedPeel.centralLog,
      MarkedC4.RDTNormalFInterface.targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using hlog _ z Nat.card_pos hz
  have hc : 4 * (d : ℝ) + 5 * (z : ℝ) ≤ 32 := by exact_mod_cast hcost
  have hzc : (z : ℝ) ≤ 4 := by exact_mod_cast hzcost
  exact ⟨⊤, inferInstance, by linarith, hzlog.trans hzc⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
