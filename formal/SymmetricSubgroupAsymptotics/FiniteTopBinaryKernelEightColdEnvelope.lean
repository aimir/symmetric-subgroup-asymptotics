import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelColdCount
import SymmetricSubgroupAsymptotics.SharpThreePointTopEpiEnvelope
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound

/-! The complete cold epimorphism estimate counts every top map and has a
strict width-twelve slope. No simultaneous-type theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopBinaryKernelEight
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
theorem cold_envelope (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤8)
    (e : (T ≃* Multiplicative (ZMod 3)) ⊕ (T ≃* Equiv.Perm (Fin 3)))
    (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      coldCoefficient top*(2 : ℝ)^(coldSlope*b) := by
  have hn := FiniteTopKernelHomLiftCount.cold_card_le top htop hK 3 hcard b J hJ
  have htop := SharpThreePointTopEpiEnvelope.epi_card_le e hKP b J
  rw [three_rpow_third_eq] at htop
  have hexp : ((3*((51*b)/200) : ℕ) : ℝ)≤(153/200)*b := by
    have hh : 200*((51*b)/200)≤51*b := by omega
    have hh' : (200 : ℝ)*((51*b)/200 : ℕ)≤51*b := by exact_mod_cast hh
    push_cast
    nlinarith
  have hp : ((2^(3*((51*b)/200)) : ℕ) : ℝ)≤
      (2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hexp
  have hn' : (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(3*((51*b)/200)) : ℕ) : ℝ) := by
    have hnreal := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_mul,mul_assoc] using hnreal
  have hcoef : 0≤SharpThreePointTopEpiEnvelope.coefficient := by
    unfold SharpThreePointTopEpiEnvelope.coefficient
    positivity
  calc
    _ ≤ _ := hn'
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(3*((51*b)/200)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htop (by positivity)) (by positivity)
    _ ≤ (SharpThreePointTopEpiEnvelope.coefficient*(2 : ℝ)^((Real.logb 2 3/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope
      rw [add_mul,Real.rpow_add (by norm_num)]
      ring
end SymmetricSubgroupAsymptotics.FiniteTopBinaryKernelEight
