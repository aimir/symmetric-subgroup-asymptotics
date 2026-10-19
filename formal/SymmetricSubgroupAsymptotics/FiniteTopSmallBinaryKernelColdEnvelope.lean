import SymmetricSubgroupAsymptotics.FiniteTopSmallBinaryKernelColdCount
import SymmetricSubgroupAsymptotics.ScalarFourCentralColdTwoCount
import SymmetricSubgroupAsymptotics.SymmetricThreeEmbeddedTopEpiEnvelope

/-! The complete cold epimorphism estimate counts every top map and has a
strict width-twelve slope. No simultaneous-type theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)

def coldCoefficient (_top : Q →* T) : ℝ := (Nat.card (T ≃* T)*Nat.card Q^Nat.card T : ℕ)
abbrev coldSlope : ℝ := ScalarFourCentralTopCoordinates.coldSlopeTwo

include htop in
theorem cold_envelope (hK : IsPGroup 2 top.ker) (hcard : Nat.card top.ker≤4)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      coldCoefficient top*(2 : ℝ)^(coldSlope*b) := by
  have hn := cold_card_le top htop hK 2 hcard b J hJ
  have htop := SymmetricThreeEmbeddedTopEpiEnvelope.epi_card_le f hf hZmud lit b J
  have hexp : ((2*((51*b)/200) : ℕ) : ℝ)≤(102/200)*b := by
    have hh : 200*((51*b)/200)≤51*b := by omega
    have hh' : (200 : ℝ)*((51*b)/200 : ℕ)≤51*b := by exact_mod_cast hh
    push_cast
    nlinarith
  have hp : ((2^(2*((51*b)/200)) : ℕ) : ℝ)≤
      (2 : ℝ)^((102/200 : ℝ)*(b : ℝ)) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hexp
  have hn' : (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(2*((51*b)/200)) : ℕ) : ℝ) := by
    have hnreal := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_mul,mul_assoc] using hnreal
  calc
    _ ≤ _ := hn'
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(2*((51*b)/200)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htop (by positivity)) (by positivity)
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((102/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope ScalarFourCentralTopCoordinates.coldSlopeTwo
      rw [Nat.cast_mul,add_mul,Real.rpow_add (by norm_num)]
      ring
end SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
