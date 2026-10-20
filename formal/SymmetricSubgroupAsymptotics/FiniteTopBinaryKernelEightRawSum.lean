import SymmetricSubgroupAsymptotics.FiniteTopBinaryKernelEightColdEnvelope
import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelRawSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo

/-! A small actual binary kernel over an actual top embedded in S3 has a
complete source sum at width twelve. All top maps and the actual source
kernels are retained, with nonsplit C4 kernels permitted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopBinaryKernelEight
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)
  (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)

include hf in
theorem small_coldCoefficient_le (hQ : Nat.card Q≤2^6) :
    coldCoefficient top≤(2 : ℝ)^(64 : ℕ) := by
  have hT := FiniteTopKernelHomLiftCount.top_card_le_six f hf
  have ha : Nat.card (DihedralGroup 3 ≃* DihedralGroup 3)≤46656 := by
    calc
      _ ≤ Nat.card (DihedralGroup 3 → DihedralGroup 3) := Nat.card_le_card_of_injective
        (fun e : DihedralGroup 3 ≃* DihedralGroup 3 => (e : DihedralGroup 3 → DihedralGroup 3)) DFunLike.coe_injective
      _ = Nat.card (DihedralGroup 3)^Nat.card (DihedralGroup 3) := Nat.card_fun
      _ = 6^6 := by norm_num [Nat.card_eq_fintype_card,DihedralGroup.card]
      _ = _ := by norm_num
  have hq : Nat.card Q^Nat.card T≤64^6 := by
    exact (Nat.pow_le_pow_left hQ _).trans
      (Nat.pow_le_pow_right (by decide : 1≤64) hT)
  have hn : (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3)+1)*Nat.card Q^Nat.card T≤2^64 :=
    (Nat.mul_le_mul (Nat.add_le_add_right ha 1) hq).trans (by norm_num)
  unfold coldCoefficient SharpThreePointTopEpiEnvelope.coefficient
  exact_mod_cast hn

include htop hf in
theorem raw_sum_le (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤8)
    (hQ : Nat.card Q≤2^6)
    (e : (T ≃* Multiplicative (ZMod 3)) ⊕ (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ))≤
      BinaryKernelRankTailNumerics.raw 1 12 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  have hc (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
      (Nat.card (GroupEpimorphism J Q) : ℝ)≤
        (2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    have hh := cold_envelope top htop hK hcard e hKP b J hJ
    have hp : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (mul_le_mul_of_nonneg_right
          coldSlope_lt.le (Nat.cast_nonneg b))
    exact hh.trans (mul_le_mul (small_coldCoefficient_le top f hf hQ) hp
      (by positivity) (by positivity))
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(64 : ℕ)) (43/30) (by positivity) hc 6 hQ b
  have ht : 6+Nat.card T≤12 := by have hT := FiniteTopKernelHomLiftCount.top_card_le_six f hf; omega
  apply hh.trans
  apply add_le_add _ le_rfl
  change (b.factorial : ℝ)^(6+Nat.card T)*_≤(1 : ℝ)*(b.factorial : ℝ)^12*_
  rw [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ _ ht
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)

end SymmetricSubgroupAsymptotics.FiniteTopBinaryKernelEight
