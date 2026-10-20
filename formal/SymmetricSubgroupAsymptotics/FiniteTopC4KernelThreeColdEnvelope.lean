import SymmetricSubgroupAsymptotics.FiniteTopC4KernelColdCount
import SymmetricSubgroupAsymptotics.SharpCyclicOrSymmetricThreeEpiEnvelope
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound

/-! Actual C4³-coordinate kernels have a strict width-twelve cold slope.
All maps to the retained or residual finite top are counted explicitly. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopC4KernelThree
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)

def coldCoefficient (_top : Q →* T) : ℝ :=
  SharpThreePointTopEpiEnvelope.coefficient*(Nat.card Q^Nat.card T : ℕ)
def coldSlope : ℝ := 153/200+Real.logb 2 3/3

theorem coldSlope_lt : coldSlope < (43 : ℝ)/30 := by
  have h := RepeatedMarkerProfileBound.logb_two_three_lt
  unfold coldSlope
  linarith

include htop in
theorem cold_envelope {c : ℕ} (hc : c≤3)
    (j : top.ker →* (Fin c → C4CoordinateHomCount.C4)) (hj : Function.Injective j)
    (hT : IsCyclic T ∨ Nonempty (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬MarkedC4KernelHotCount.KernelHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      coldCoefficient top*(2 : ℝ)^(coldSlope*b) := by
  have hn := FiniteTopC4KernelColdCount.cold_card_le top htop j hj b J hJ
  have ht := SharpCyclicOrSymmetricThreeEpiEnvelope.epi_card_le hT hKP b J
  rw [three_rpow_third_eq] at ht
  have hcR : (c : ℝ)≤3 := by exact_mod_cast hc
  have hp : (2 : ℝ)^(((51/200 : ℝ)*c)*b) ≤ (2 : ℝ)^((153/200 : ℝ)*b) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg b))
  calc
    _ ≤ _ := hn
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by
        have hn := Nat.cast_nonneg (α := ℝ) (Nat.card (DihedralGroup 3 ≃* DihedralGroup 3))
        unfold SharpThreePointTopEpiEnvelope.coefficient
        positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope
      rw [add_mul,Real.rpow_add (by norm_num)]
      ring
end SymmetricSubgroupAsymptotics.FiniteTopC4KernelThree
