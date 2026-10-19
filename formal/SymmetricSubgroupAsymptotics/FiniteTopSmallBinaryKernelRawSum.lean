import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelColdEnvelope
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo

/-! A small actual binary kernel over an actual top embedded in S3 has a
complete source sum at width twelve. All top maps and the actual source
kernels are retained, with nonsplit C4 kernels permitted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)
  (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)

include hf in
theorem top_card_le_six : Nat.card T≤6 := by
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_perm,Nat.card_fin] using h

include hf in
theorem small_coldCoefficient_le (hQ : Nat.card Q≤2^5) :
    coldCoefficient top≤(2 : ℝ)^(64 : ℕ) := by
  have hT := top_card_le_six f hf
  have ha : Nat.card (T ≃* T)≤46656 := by
    calc
      _ ≤ Nat.card (T → T) := Nat.card_le_card_of_injective
        (fun e : T ≃* T => (e : T → T)) DFunLike.coe_injective
      _ = Nat.card T^Nat.card T := Nat.card_fun
      _ ≤ 6^Nat.card T := Nat.pow_le_pow_left hT _
      _ ≤ 6^6 := Nat.pow_le_pow_right (by decide : 1≤6) hT
      _ = _ := by norm_num
  have hq : Nat.card Q^Nat.card T≤32^6 := by
    exact (Nat.pow_le_pow_left hQ _).trans
      (Nat.pow_le_pow_right (by decide : 1≤32) hT)
  have hn : Nat.card (T ≃* T)*Nat.card Q^Nat.card T≤2^64 :=
    (Nat.mul_le_mul ha hq).trans (by norm_num)
  unfold coldCoefficient
  exact_mod_cast hn

include htop hf in
theorem raw_sum_le (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤4)
    (hQ : Nat.card Q≤2^5)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ))≤
      BinaryKernelRankTailNumerics.raw 1 11 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  have hc (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
      (Nat.card (GroupEpimorphism J Q) : ℝ)≤
        (2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    have hh := cold_envelope top htop hK hcard f hf hZmud lit b J hJ
    have hp : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (mul_le_mul_of_nonneg_right
          ScalarFourCentralTopCoordinates.coldSlopeTwo_le_width_twelve (Nat.cast_nonneg b))
    exact hh.trans (mul_le_mul (small_coldCoefficient_le top f hf hQ) hp
      (by positivity) (by positivity))
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(64 : ℕ)) (43/30) (by positivity) hc 5 hQ b
  have ht : 5+Nat.card T≤11 := by have hT := top_card_le_six f hf; omega
  apply hh.trans
  apply add_le_add _ le_rfl
  change (b.factorial : ℝ)^(5+Nat.card T)*_≤(1 : ℝ)*(b.factorial : ℝ)^11*_
  rw [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ _ ht
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)

end SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
