import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource

/-!
# Sharper nonsoluble affine numerics below degree 128

The general large-degree comparison deliberately uses a coarse linear bound
for `log₂ w`.  At degrees 32, 49, 64 and 81 the integral composition charge
from the actual chief trace gives a stronger bound.  These are direct
consequences of the published primitive composition-length inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem fixedTargetCompositionGamma_lt_eight_fifteenths :
    fixedTargetCompositionGamma < (8 : ℝ) / 15 := by
  unfold fixedTargetCompositionGamma
  have h := RepeatedMarkerProfileBound.logb_two_three_lt
  linarith

namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- An integral bound on the number of abelian complement edges gives the
exact physical exponent margin once its elementary numerical inequality is
checked. -/
theorem nonsolubleEnvelope_exponent_margin_of_abelianLength
    {G : Type} [Group G] [Finite G]
    {w A : ℕ} (T : FixedTargetCompositionTrace G)
    (hlen : T.envelope.abelianLength ≤ A)
    (hnum : Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w +
        ((8 : ℝ) / 15) * (A + (1 : ℝ) / 2) ≤
      ((evenWidth w : ℝ) - 2) / 8) :
    Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 -
        (fixedTargetCompositionGamma * T.envelope.abelianLength +
          P.bottomHalfSlope) := by
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    have := half_le_logThreeThird
    linarith
  have hlenR : (T.envelope.abelianLength : ℝ) ≤ A := by
    exact_mod_cast hlen
  have hab : fixedTargetCompositionGamma * T.envelope.abelianLength ≤
      fixedTargetCompositionGamma * A :=
    mul_le_mul_of_nonneg_left hlenR hgamma0
  have hbottom := P.bottomHalfSlope_le_fixedTargetGamma_half
  have heta : fixedTargetCompositionGamma * T.envelope.abelianLength +
      P.bottomHalfSlope ≤
      fixedTargetCompositionGamma * (A + (1 : ℝ) / 2) := by
    calc
      _ ≤ fixedTargetCompositionGamma * A +
          fixedTargetCompositionGamma / 2 := add_le_add hab hbottom
      _ = _ := by ring
  have hbracket : 0 ≤ (A : ℝ) + 1 / 2 := by positivity
  have hgamma := fixedTargetCompositionGamma_lt_eight_fifteenths
  have heta' := heta.trans
    (mul_le_mul_of_nonneg_right hgamma.le hbracket)
  nlinarith

end PrimitiveAffineProfile

private theorem logb_two_thirtyTwo : Real.logb 2 (32 : ℝ) = 5 := by
  rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

private theorem logb_two_sixtyFour : Real.logb 2 (64 : ℝ) = 6 := by
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

private theorem logb_two_fortyNine_lt :
    Real.logb 2 (49 : ℝ) < (45 : ℝ) / 8 := by
  have hpowNat : 7 ^ 16 < 2 ^ 45 := by norm_num
  have hpow : ((7 : ℝ) ^ (16 : ℕ)) < (2 : ℝ) ^ (45 : ℕ) := by
    exact_mod_cast hpowNat
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 7) 16) hpow
  rw [Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
  have h49 : Real.logb 2 (49 : ℝ) = 2 * Real.logb 2 7 := by
    rw [show (49 : ℝ) = 7 ^ (2 : ℕ) by norm_num, Real.logb_pow]
    norm_num
  rw [h49]
  norm_num at hlog ⊢
  linarith

private theorem logb_two_eightyOne_lt :
    Real.logb 2 (81 : ℝ) < 7 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 81) (by norm_num : (81 : ℝ) < 128)
  rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at h
  norm_num at h ⊢
  exact h

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineNonsolubleSmallNumerics

open PrimitiveAffineProfile

private theorem length_le_six_at_32
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 32)
    (P : PrimitiveAffineProfile (preE7NonPairAction 32 U) (Fin 32))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 32 U) (Fin 32))
    (x : Fin 32) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 6 := by
  have hd : C.d = 5 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 2) (by norm_num) (by norm_num)
  have hcharge := P.complementTrace_charge_le_primitiveBound hcomp
    (by norm_num) (preE7NonPairAction 32 U) hprimitive x C T hnonsolvable
  norm_num only [Nat.cast_ofNat] at hcharge
  rw [logb_two_thirtyTwo, hd] at hcharge
  norm_num at hcharge
  have hnat : T.envelope.abelianLength + 5 + 1 ≤ 12 := by
    exact_mod_cast hcharge
  omega

private theorem length_le_ten_at_49
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 49)
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 49 U) (Fin 49))
    (x : Fin 49) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 10 := by
  have hd : C.d = 2 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num)
  have hcharge := P.complementTrace_charge_le_primitiveBound hcomp
    (by norm_num) (preE7NonPairAction 49 U) hprimitive x C T hnonsolvable
  rw [hd] at hcharge
  have hlog := logb_two_fortyNine_lt
  have hstrict : ((T.envelope.abelianLength + 2 + 1 : ℕ) : ℝ) < 14 := by
    nlinarith
  have hnat : T.envelope.abelianLength + 2 + 1 < 14 := by
    exact_mod_cast hstrict
  omega

private theorem length_le_seven_at_64
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 64)
    (P : PrimitiveAffineProfile (preE7NonPairAction 64 U) (Fin 64))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 64 U) (Fin 64))
    (x : Fin 64) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 7 := by
  have hd : C.d = 6 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 2) (by norm_num) (by norm_num)
  have hcharge := P.complementTrace_charge_le_primitiveBound hcomp
    (by norm_num) (preE7NonPairAction 64 U) hprimitive x C T hnonsolvable
  norm_num only [Nat.cast_ofNat] at hcharge
  rw [logb_two_sixtyFour, hd] at hcharge
  norm_num at hcharge
  have hstrict : ((T.envelope.abelianLength + 6 + 1 : ℕ) : ℝ) < 15 := by
    rw [Nat.cast_add, Nat.cast_add]
    norm_num
    exact hcharge.trans_lt (by norm_num : (44 : ℝ) / 3 < 15)
  have hnat : T.envelope.abelianLength + 6 + 1 < 15 := by
    exact_mod_cast hstrict
  omega

private theorem length_le_twelve_at_81
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength ≤ 12 := by
  have hd : C.d = 4 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 3) (by norm_num) (by norm_num)
  have hcharge := P.complementTrace_charge_le_primitiveBound hcomp
    (by norm_num) (preE7NonPairAction 81 U) hprimitive x C T hnonsolvable
  rw [hd] at hcharge
  have hlog := logb_two_eightyOne_lt
  have hstrict : ((T.envelope.abelianLength + 4 + 1 : ℕ) : ℝ) < 18 := by
    nlinarith
  have hnat : T.envelope.abelianLength + 4 + 1 < 18 := by
    exact_mod_cast hstrict
  omega

theorem exponent_margin_32
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 32)
    (P : PrimitiveAffineProfile (preE7NonPairAction 32 U) (Fin 32))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 32 U) (Fin 32))
    (x : Fin 32) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 32 ≤ ((evenWidth 32 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 32) (A := 6) T
    (length_le_six_at_32 hcomp U P hprimitive x C T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

theorem exponent_margin_49
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 49)
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 49 U) (Fin 49))
    (x : Fin 49) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 49 ≤ ((evenWidth 49 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 49) (A := 10) T
    (length_le_ten_at_49 hcomp U P hprimitive x C T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

theorem exponent_margin_64
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 64)
    (P : PrimitiveAffineProfile (preE7NonPairAction 64 U) (Fin 64))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 64 U) (Fin 64))
    (x : Fin 64) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 64 ≤ ((evenWidth 64 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 64) (A := 7) T
    (length_le_seven_at_64 hcomp U P hprimitive x C T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

theorem exponent_margin_81
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 81 ≤ ((evenWidth 81 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 81) (A := 12) T
    (length_le_twelve_at_81 hcomp U P hprimitive x C T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

end PrimitiveAffineNonsolubleSmallNumerics
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
