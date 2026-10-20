import SymmetricSubgroupAsymptotics.ScalarFourCentralColdCount
import SymmetricSubgroupAsymptotics.SymmetricThreeEmbeddedTopEpiEnvelope

/-! The complete cold epimorphism estimate counts every top map and has a
strict width-sixteen slope. No simultaneous-type theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

def coldCoefficient (_D : ScalarFourCentralTopCoordinates Q T c d) : ℝ := (Nat.card (T ≃* T)*Nat.card Q^Nat.card T : ℕ)
def coldSlope : ℝ := 153/200+Real.logb 2 5/3

theorem cold_envelope (hc : c≤3) (hd : d≤3)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      D.coldCoefficient*(2 : ℝ)^(coldSlope*b) := by
  have hn := D.cold_card_le hc hd b J hJ
  have htop := SymmetricThreeEmbeddedTopEpiEnvelope.epi_card_le f hf hZmud lit b J
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
  calc
    _ ≤ _ := hn'
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(3*((51*b)/200)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htop (by positivity)) (by positivity)
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope
      rw [Nat.cast_mul,add_mul,Real.rpow_add (by norm_num)]
      ring
end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
