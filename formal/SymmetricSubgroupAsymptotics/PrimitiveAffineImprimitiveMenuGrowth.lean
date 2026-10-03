import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient
import SymmetricSubgroupAsymptotics.GrowingMenuMassSubquadraticLogSquared

/-!
# Subquadratic menu growth of the imprimitive affine coefficient

The actual local-chief tower has a width-only coefficient cost plus a
linear source logarithm.  This file proves that the width-only cost is
`o(w^2)` and packages the resulting uniform menu envelope.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private theorem eventually_log_four_le_sqrt
    (C : ℝ) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log ((n : ℝ) + 2) ^ 4 ≤ ε * Real.sqrt (n : ℝ) := by
  let δ : ℝ := min 1 (ε / (4 * (C + 1)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (4 * (C + 1)) := min_le_right _ _
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog := ((_root_.isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 8)).bound hδ)
  filter_upwards [hshift.eventually hlog, eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1R : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : 0 ≤ (n : ℝ) + 2 := by positivity
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hrpow0 : 0 ≤ ((n : ℝ) + 2) ^ (1 / 8 : ℝ) := by positivity
  have hlogbound : Real.log ((n : ℝ) + 2) ≤
      δ * ((n : ℝ) + 2) ^ (1 / 8 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hrpow0] using hn
  have hpow := pow_le_pow_left₀ hlog0 hlogbound 4
  have hrpow : (((n : ℝ) + 2) ^ (1 / 8 : ℝ)) ^ (4 : ℕ) =
      Real.sqrt ((n : ℝ) + 2) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx0]
    norm_num [Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt ((n : ℝ) + 2) ≤ 2 * Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hn0]
  have hδpow : δ ^ 4 ≤ δ := by
    calc
      δ ^ 4 = δ * δ ^ 3 := by ring
      _ ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδ1) hδ.le
      _ = δ := mul_one _
  have hcoef : 2 * C * δ ^ 4 ≤ ε := by
    have hCle : C ≤ C + 1 := by linarith
    have hden : 0 < 4 * (C + 1) := by positivity
    have hδε' : 4 * (C + 1) * δ ≤ ε :=
      by simpa [mul_comm] using (le_div_iff₀ hden).mp hδε
    nlinarith [mul_nonneg hC hδ.le]
  calc
    C * Real.log ((n : ℝ) + 2) ^ 4 ≤
        C * (δ * ((n : ℝ) + 2) ^ (1 / 8 : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * δ ^ 4 * Real.sqrt ((n : ℝ) + 2) := by
      rw [mul_pow, hrpow]
      ring
    _ ≤ C * δ ^ 4 * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hC (pow_nonneg hδ.le _))
    _ = (2 * C * δ ^ 4) * Real.sqrt (n : ℝ) := by ring
    _ ≤ ε * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- The integer binary logarithm occurring in the local-order budget is
controlled by the ordinary real logarithm used by the menu theorem. -/
private theorem natLogSucc_four_le_log_four (w : ℕ) (hw : 1 ≤ w) :
    (((Nat.log 2 w + 1 : ℕ) : ℝ) ^ 4) ≤
      (2 / Real.log 2) ^ 4 * Real.log ((w : ℝ) + 2) ^ 4 := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hwshift : (w : ℝ) ≤ (w : ℝ) + 2 := by linarith
  have hlogb := Real.natLog_le_logb w 2
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hwpos hwshift
  have hbase : (1 : ℝ) ≤ Real.logb 2 ((w : ℝ) + 2) := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ (w : ℝ) + 2 by linarith)
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using this
  have hsum : ((Nat.log 2 w + 1 : ℕ) : ℝ) ≤
      2 * Real.logb 2 ((w : ℝ) + 2) := by
    calc
      ((Nat.log 2 w + 1 : ℕ) : ℝ) = (Nat.log 2 w : ℝ) + 1 := by norm_num
      _ ≤ Real.logb 2 ((w : ℝ) + 2) + 1 := by
        linarith [hlogb.trans hmono]
      _ ≤ 2 * Real.logb 2 ((w : ℝ) + 2) := by linarith
  have hlogb0 : 0 ≤ Real.logb 2 ((w : ℝ) + 2) := by linarith
  calc
    (((Nat.log 2 w + 1 : ℕ) : ℝ) ^ 4) ≤
        (2 * Real.logb 2 ((w : ℝ) + 2)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hsum 4
    _ = (2 / Real.log 2) ^ 4 * Real.log ((w : ℝ) + 2) ^ 4 := by
      rw [Real.logb]
      ring

/-- The width-only affine cost is eventually an arbitrarily small multiple
of `w^2`. -/
theorem eventually_affineComponentWidthCost_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w : ℕ in atTop,
      affineComponentWidthCost w ≤ ε * (w : ℝ) ^ 2 := by
  let C : ℝ := 100 * (2 / Real.log 2) ^ 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog := eventually_log_four_le_sqrt C hC
    (show 0 < ε / 3 by positivity)
  have htLog : Tendsto (fun w : ℕ => Real.logb 2 (w : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop
  have htHalf : Tendsto (fun w : ℕ => Real.logb 2 (w : ℝ) / 2)
      atTop atTop := Tendsto.atTop_div_const (by norm_num) htLog
  have htSqrt : Tendsto
      (fun w : ℕ => Real.sqrt (Real.logb 2 (w : ℝ) / 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp htHalf
  have hden := htSqrt.eventually_ge_atTop (300 / ε)
  filter_upwards [hlog, hden, eventually_ge_atTop 1] with w hlogw hdenw hw
  let X : ℝ := w
  let L : ℝ := ((Nat.log 2 w + 1 : ℕ) : ℝ) ^ 2
  let q : ℝ := Real.sqrt (Real.logb 2 X / 2)
  have hX0 : 0 ≤ X := by positivity
  have hX1 : 1 ≤ X := by dsimp [X]; exact_mod_cast hw
  have hsqrt1 : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX1
  have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0
  have hL1 : 1 ≤ L := by
    dsimp [L]
    have : (1 : ℝ) ≤ ((Nat.log 2 w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ Nat.log 2 w + 1 by omega)
    nlinarith
  have hLsq : 100 * L ^ 2 ≤ (ε / 3) * Real.sqrt X := by
    have hnat := natLogSucc_four_le_log_four w hw
    have hscaled : 100 * L ^ 2 ≤ C * Real.log ((w : ℝ) + 2) ^ 4 := by
      dsimp [L, C]
      convert mul_le_mul_of_nonneg_left hnat (show (0 : ℝ) ≤ 100 by norm_num)
        using 1 <;> ring
    exact hscaled.trans hlogw
  have hfirst : 100 * X * Real.sqrt X * L ^ 2 ≤
      (ε / 3) * X ^ 2 := by
    have hsqrtMul : Real.sqrt X * Real.sqrt X = X := by
      simpa only [pow_two] using hsqrtSq
    calc
      100 * X * Real.sqrt X * L ^ 2 =
          X * Real.sqrt X * (100 * L ^ 2) := by ring
      _ ≤ X * Real.sqrt X * ((ε / 3) * Real.sqrt X) := by gcongr
      _ = (ε / 3) * X * (Real.sqrt X * Real.sqrt X) := by ring
      _ = (ε / 3) * X ^ 2 := by rw [hsqrtMul]; ring
  have hdenpos : 0 < q := by
    have : 0 < 300 / ε := div_pos (by norm_num) hε
    exact this.trans_le (by simpa [q, X] using hdenw)
  have hthree : 300 ≤ ε * q := by
    have := (div_le_iff₀ hε).mp (show 300 / ε ≤ q by
      simpa [q, X] using hdenw)
    nlinarith
  have hfrac : 100 / q ≤ ε / 3 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hsecond : 100 * X ^ 2 / q ≤ (ε / 3) * X ^ 2 := by
    calc
      100 * X ^ 2 / q = (100 / q) * X ^ 2 := by ring
      _ ≤ (ε / 3) * X ^ 2 :=
        mul_le_mul_of_nonneg_right hfrac (sq_nonneg X)
  have hthird : 100 * X * L ≤ (ε / 3) * X ^ 2 := by
    have hLle : L ≤ L ^ 2 := by nlinarith
    have haux : 100 * L ≤ (ε / 3) * X := by
      calc
        100 * L ≤ 100 * L ^ 2 := by nlinarith
        _ ≤ (ε / 3) * Real.sqrt X := hLsq
        _ ≤ (ε / 3) * X :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left haux hX0]
  dsimp [affineComponentWidthCost, X, L, q]
  nlinarith

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
