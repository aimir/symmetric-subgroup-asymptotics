import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleFibreEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7NonsolublePrimitiveAffine

/-!
# Numerical margin for nonsoluble primitive-affine actions

The exponent in the complete fibre envelope is compared with the published
primitive composition-length bound.  From degree `128` onward a completely
elementary logarithm estimate puts it inside the global pre-`E7` window.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomHalfSlope_le_fixedTargetGamma_half :
    P.bottomHalfSlope ≤ fixedTargetCompositionGamma / 2 := by
  have h := prime_log_slope_le_fixedTargetGamma P.p P.p_prime
  unfold bottomHalfSlope
  calc
    Real.logb 2 P.p / (2 * (P.p : ℝ)) =
        (Real.logb 2 P.p / P.p) / 2 := by ring
    _ ≤ fixedTargetCompositionGamma / 2 := by gcongr

/-- The exact exponent inequality obtained from the nonsoluble saved
composition edge. -/
theorem nonsolubleEnvelopeSlope_le_compositionBound
    (hcomp : PrimitiveCompositionLengthInput)
    {w : ℕ} (hw : 2 ≤ w)
    (U : Subgroup (Equiv.Perm (Fin w))) [Nontrivial (Fin w)]
    (A : PrimitiveAffineProfile U (Fin w))
    (hprimitive : MulAction.IsPreprimitive U (Fin w))
    (x : Fin w) (C : A.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (A.complement x))
    (hnonsolvable : ¬ IsSolvable (A.complement x)) :
    fixedTargetCompositionGamma * T.envelope.abelianLength +
        A.bottomHalfSlope ≤
      fixedTargetCompositionGamma *
        ((8 / 3 : ℝ) * Real.logb 2 w - C.d - 11 / 6) := by
  have hcharge := A.complementTrace_charge_le_primitiveBound hcomp hw U
    hprimitive x C T hnonsolvable
  have hgamma : 0 ≤ fixedTargetCompositionGamma :=
    (half_le_logThreeThird.trans_eq rfl).trans' (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hcharge hgamma
  have hbottom := A.bottomHalfSlope_le_fixedTargetGamma_half
  push_cast at hscaled
  nlinarith

end PrimitiveAffineProfile

private theorem sixteen_mul_add_fifteen_le_pow
    {n : ℕ} (hn : 8 ≤ n) : 16 * n + 15 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        16 * (n + 1) + 15 ≤ 2 * (16 * n + 15) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- A convenient elementary linear bound for the binary logarithm. -/
theorem logb_two_nat_le_sixteenth {w : ℕ} (hw : 128 ≤ w) :
    Real.logb 2 w ≤ (w : ℝ) / 16 := by
  have hdiv : 8 ≤ w / 16 := by omega
  have hrem : w ≤ 16 * (w / 16) + 15 := by omega
  have hpow : w ≤ 2 ^ (w / 16) :=
    hrem.trans (sixteen_mul_add_fifteen_le_pow hdiv)
  have hclog : Nat.clog 2 w ≤ w / 16 :=
    Nat.clog_le_of_le_pow hpow
  calc
    Real.logb 2 w ≤ (⌈Real.logb 2 w⌉₊ : ℝ) := Nat.le_ceil _
    _ = (Nat.clog 2 w : ℝ) := by
      norm_cast
    _ ≤ (w / 16 : ℕ) := by exact_mod_cast hclog
    _ ≤ (w : ℝ) / 16 := Nat.cast_div_le

private theorem fixedTargetCompositionGamma_lt_eight_fifteenths :
    fixedTargetCompositionGamma < (8 : ℝ) / 15 := by
  unfold fixedTargetCompositionGamma
  have h := RepeatedMarkerProfileBound.logb_two_three_lt
  linarith

/-- Every nonsoluble primitive-affine exponent from degree `128` onward has
the full global `ρ = 1/8192` margin. -/
theorem PrimitiveAffineProfile.nonsolubleEnvelope_exponent_margin_large
    (hcomp : PrimitiveCompositionLengthInput)
    {w : ℕ} (hw : 128 ≤ w)
    (U : Subgroup (Equiv.Perm (Fin w))) [Nontrivial (Fin w)]
    (A : PrimitiveAffineProfile U (Fin w))
    (hprimitive : MulAction.IsPreprimitive U (Fin w))
    (x : Fin w) (C : A.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (A.complement x))
    (hnonsolvable : ¬ IsSolvable (A.complement x)) :
    Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 -
        (fixedTargetCompositionGamma * T.envelope.abelianLength +
          A.bottomHalfSlope) := by
  have heta := A.nonsolubleEnvelopeSlope_le_compositionBound hcomp
    (by omega) U hprimitive x C T hnonsolvable
  have hlog := logb_two_nat_le_sixteenth hw
  have hd : (1 : ℝ) ≤ C.d := by exact_mod_cast C.d_pos
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    have := half_le_logThreeThird
    simpa [fixedTargetCompositionGamma] using this.trans' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have harg :
      (8 / 3 : ℝ) * Real.logb 2 w - C.d - 11 / 6 ≤
        (w : ℝ) / 6 - 17 / 6 := by
    nlinarith
  have heta' := heta.trans (mul_le_mul_of_nonneg_left harg hgamma0)
  have hbracket : 0 ≤ (w : ℝ) / 6 - 17 / 6 := by
    have hwR : (128 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have hgamma := fixedTargetCompositionGamma_lt_eight_fifteenths
  have heta'' :
      fixedTargetCompositionGamma * T.envelope.abelianLength +
          A.bottomHalfSlope ≤
        (8 / 15 : ℝ) * ((w : ℝ) / 6 - 17 / 6) :=
    heta'.trans (mul_le_mul_of_nonneg_right hgamma.le hbracket)
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  unfold Non2UnipotentPrefixFiniteMenu.preE7CharacterRho
  norm_num at *
  nlinarith

end SymmetricSubgroupAsymptotics

end
