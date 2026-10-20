import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelColdCount
import SymmetricSubgroupAsymptotics.FiniteTopC4KernelThreeRawSum
import SymmetricSubgroupAsymptotics.SharpCyclicOrSymmetricThreeEpiEnvelope
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold

/-! Actual binary kernels with dual module generation at most two have a strict width-twelve cold slope.
All maps to the retained or residual finite top are counted explicitly. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelTwo
open scoped BigOperators
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)
  (A : Rep.{0} (ZMod 2) T) (E : OriginalKernelModuleChart top A)

def coldCoefficient (_top : Q →* T) : ℝ :=
  SharpThreePointTopEpiEnvelope.coefficient*(Nat.card Q^Nat.card T : ℕ)
def coldSlope : ℝ := 102/200+Real.logb 2 3/3

theorem coldSlope_lt : coldSlope < (43 : ℝ)/30 := by
  have h := RepeatedMarkerProfileBound.logb_two_three_lt
  unfold coldSlope
  linarith

include htop E in
theorem cold_envelope (hgen : RepresentationGeneratedBy A.ρ.dual 2)
    (hT : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      coldCoefficient top*(2 : ℝ)^(coldSlope*b) := by
  have hn := FiniteTopBinaryDualKernelColdCount.cold_card_le top htop A E hgen b J hJ
  have ht := SharpCyclicOrSymmetricThreeEpiEnvelope.epi_card_le hT hKP b J
  rw [three_rpow_third_eq] at ht
  have hp : (2 : ℝ)^(((51/200 : ℝ)*2)*b) ≤ (2 : ℝ)^((102/200 : ℝ)*b) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc
    _ ≤ _ := hn
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^(((51/200 : ℝ)*2)*b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((102/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by
        have hn := Nat.cast_nonneg (α := ℝ) (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3))
        unfold SharpThreePointTopEpiEnvelope.coefficient
        positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope
      rw [add_mul,Real.rpow_add (by norm_num)]
      ring

include htop E in
theorem raw_sum_le (hgen : RepresentationGeneratedBy A.ρ.dual 2)
    (hTcard : Nat.card T≤6) (hQ : Nat.card Q≤2^9)
    (hT : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ))≤
      BinaryKernelRankTailNumerics.raw 1 15 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))) := by
  have hc (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
      (Nat.card (GroupEpimorphism J Q) : ℝ)≤
        (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
    have hh := cold_envelope top htop A E hgen hT hKP b J hJ
    have hp : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (mul_le_mul_of_nonneg_right coldSlope_lt.le (Nat.cast_nonneg b))
    have hcoef : coldCoefficient top≤(2 : ℝ)^(80 : ℕ) :=
      FiniteTopC4KernelThree.small_coldCoefficient_le top hTcard hQ
    exact hh.trans (mul_le_mul hcoef hp (by positivity) (by positivity))
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(80 : ℕ)) (43/30) (by positivity) hc 9 hQ b
  have ht : 9+Nat.card T≤15 := by omega
  apply hh.trans
  apply add_le_add _ le_rfl
  unfold BinaryKernelRankTailNumerics.raw
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ _ ht
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)

end SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelTwo
