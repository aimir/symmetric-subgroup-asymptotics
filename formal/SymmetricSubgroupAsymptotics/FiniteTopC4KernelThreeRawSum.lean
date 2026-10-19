import SymmetricSubgroupAsymptotics.FiniteTopC4KernelThreeColdEnvelope
import SymmetricSubgroupAsymptotics.MarkedC4KernelHotCount
import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelRawSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo

/-! Complete source sums for actual C4³-coordinate kernels and small
cyclic or symmetric-three tops. The hot branch uses the whole C4 moment
on the same actual finite-index source kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopC4KernelThree
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)
  (hTcard : Nat.card T≤6)

omit [Finite Q] [Finite T] in
include hTcard in
theorem small_coldCoefficient_le (hQ : Nat.card Q≤2^9) :
    coldCoefficient top≤(2 : ℝ)^(80 : ℕ) := by
  have hT := hTcard
  have ha : Nat.card (DihedralGroup 3 ≃* DihedralGroup 3)≤46656 := by
    calc
      _ ≤ Nat.card (DihedralGroup 3 → DihedralGroup 3) := Nat.card_le_card_of_injective
        (fun e : DihedralGroup 3 ≃* DihedralGroup 3 => (e : DihedralGroup 3 → DihedralGroup 3)) DFunLike.coe_injective
      _ = Nat.card (DihedralGroup 3)^Nat.card (DihedralGroup 3) := Nat.card_fun
      _ = 6^6 := by norm_num [Nat.card_eq_fintype_card,DihedralGroup.card]
      _ = _ := by norm_num
  have hq : Nat.card Q^Nat.card T≤512^6 := by
    exact (Nat.pow_le_pow_left hQ _).trans
      (Nat.pow_le_pow_right (by decide : 1≤512) hT)
  have hn : (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3)+1)*Nat.card Q^Nat.card T≤2^80 :=
    (Nat.mul_le_mul (Nat.add_le_add_right ha 1) hq).trans (by norm_num)
  unfold coldCoefficient SharpThreePointTopEpiEnvelope.coefficient
  exact_mod_cast hn

include htop hTcard in
theorem raw_sum_le {c : ℕ} (hc : c≤3)
    (j : top.ker →* (Fin c → C4CoordinateHomCount.C4)) (hj : Function.Injective j)
    (hQ : Nat.card Q≤2^9)
    (hT : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ))≤
      MarkedC4KernelRankTailNumerics.raw 1 15 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  have hcold_bound (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (hJ : ¬MarkedC4KernelHotCount.KernelHot T (51/200) J) :
      (Nat.card (GroupEpimorphism J Q) : ℝ)≤
        (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    have hh := cold_envelope top htop hc j hj hT hKP b J hJ
    have hp : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (mul_le_mul_of_nonneg_right
          coldSlope_lt.le (Nat.cast_nonneg b))
    exact hh.trans (mul_le_mul (small_coldCoefficient_le top hTcard hQ) hp
      (by positivity) (by positivity))
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop :=
    MarkedC4KernelHotCount.KernelHot T (51/200)
  have hh := MarkedC4KernelHotCount.kernel_hot_epi_sum_le T Q 9 hQ b
  have hh' : (∑ J ∈ Finset.univ.filter hot,(Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      MarkedC4KernelRankTailNumerics.raw 1 15 b := by
    apply hh.trans
    have ht : 9+Nat.card T≤15 := by omega
    have hm : 0 ≤ markedC4Moment b (MarkedC4KernelRankTailNumerics.tilt b) := by
      unfold markedC4Moment
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    unfold MarkedC4KernelRankTailNumerics.raw
    simp only [one_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_right₀ _ ht
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
  have hcold : (∑ J ∈ Finset.univ.filter (fun J => ¬hot J),
      (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
    calc
      _ ≤ ∑ _J ∈ Finset.univ.filter (fun J => ¬hot J),
          (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact hcold_bound b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)),
          (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp [subgroupCount]
  rw [←Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  exact add_le_add hh' hcold

end SymmetricSubgroupAsymptotics.FiniteTopC4KernelThree
