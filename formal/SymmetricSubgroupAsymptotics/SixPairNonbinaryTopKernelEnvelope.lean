import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorEnvelope
import SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! The original six-pair target has order below 2^16 and its actual
residual top has order at most 6!. Using the logarithm of the top order
keeps the complete coefficient inside the existing width-twelve menu.
All top maps and all exceptional finite-index kernels are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairNonbinaryTopKernelEnvelope
open Non2UnipotentPrefixFiniteMenu

variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]

theorem coefficient_le (hQ : Nat.card Q ≤ 2^16) (hT : Nat.card T ≤ 720) :
    ((Nat.card Q^Nat.log 2 (Nat.card T) : ℕ) : ℝ) * (Nat.card (T ≃* T) : ℝ) ≤
      (2 : ℝ)^(234 : ℕ) := by
  have hlog : Nat.log 2 (Nat.card T) ≤ 9 := by
    have hh : Nat.card T < 2^10 := hT.trans_lt (by norm_num)
    have hl := Nat.log_lt_of_lt_pow (Nat.card_pos (α := T)).ne' hh
    omega
  have hp : Nat.card Q^Nat.log 2 (Nat.card T) ≤ 2^144 := by
    calc
      _ ≤ (2^16)^Nat.log 2 (Nat.card T) := Nat.pow_le_pow_left hQ _
      _ ≤ (2^16)^9 := Nat.pow_le_pow_right (by norm_num) hlog
      _ = _ := by rw [←pow_mul]
  have ha : Nat.card (T ≃* T) ≤ 2^90 := by
    apply (mulEquiv_card_le_card_pow_log T).trans
    calc
      _ ≤ (2^10)^Nat.log 2 (Nat.card T) := Nat.pow_le_pow_left (hT.trans (by norm_num)) _
      _ ≤ (2^10)^9 := Nat.pow_le_pow_right (by norm_num) hlog
      _ = _ := by rw [←pow_mul]
  have hn := Nat.mul_le_mul hp ha
  rw [show (2^144 : ℕ)*2^90=2^234 by rw [←pow_add]] at hn
  exact_mod_cast hn

variable (top : Q →* T) (htop : Function.Surjective top)
    (A : Rep.{0} (ZMod 2) T) (E : OriginalKernelModuleChart top A)

include htop E in
theorem cold_card_le
    (hgen : RepresentationGeneratedBy A.ρ.dual 2)
    (hQ : Nat.card Q ≤ 2^16) (hT : Nat.card T ≤ 720)
    (hsocle : SocleNormalGeneratorBound T 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (2 : ℝ)^(234 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*b) := by
  have h := FiniteTopBinaryDualKernelGeneratorColdCount.cold_card_le
    top htop A E hgen b J hJ
  have hc : (Nat.card (GroupEpimorphism J T) : ℝ) ≤
      (Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b) := by
    simpa only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
      Nat.cast_one,one_mul] using (hZmud.generalCertificate hsocle).envelope lit b J
  have he : (Real.logb 2 5/3)*b+((51/200 : ℝ)*2)*b ≤ (43/30 : ℝ)*b := by
    have h0 := PairedEightTopCostNumerics.ordinary_le
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith
  calc
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
          (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*2)*b) :=
      h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))
    _ = ((Nat.card Q^Nat.log 2 (Nat.card T) : ℕ) : ℝ)*(Nat.card (T ≃* T) : ℝ)*
          (2 : ℝ)^((Real.logb 2 5/3)*b+((51/200 : ℝ)*2)*b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ (2 : ℝ)^(234 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*b) :=
      mul_le_mul (coefficient_le hQ hT)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by positivity) (by positivity)

include htop E in
theorem raw_sum_le
    (hgen : RepresentationGeneratedBy A.ρ.dual 2)
    (hQ : Nat.card Q ≤ 2^16) (hT : Nat.card T ≤ 720)
    (hsocle : SocleNormalGeneratorBound T 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 736 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(234 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*b)) := by
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(234 : ℕ)) (43/30) (by positivity)
    (fun b J hJ => cold_card_le top htop A E hgen hQ hT hsocle hZmud lit b J hJ) 16 hQ b
  apply hh.trans
  apply add_le_add _ le_rfl
  change (b.factorial : ℝ)^(16+Nat.card T)*_ ≤ (1 : ℝ)*(b.factorial : ℝ)^736*_
  rw [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos b))
    (by omega : 16+Nat.card T≤736)

end SymmetricSubgroupAsymptotics.SixPairNonbinaryTopKernelEnvelope
