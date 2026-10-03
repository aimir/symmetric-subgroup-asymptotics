import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentTransfer
import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficient
import SymmetricSubgroupAsymptotics.AffineComponentWidthCost

/-!
# Uniform coefficient of an actual imprimitive affine component

The actual local-chief tower retains the elementary and nonabelian order
budgets separately.  Their sum is the exact base-two logarithm of the
literal primitive component.  The primitive affine order theorem therefore
bounds both budgets by the logarithmic-square expression in the literal
block degree, without replacing the component by a catalogue action.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Elementary logarithmic-square domination, uniform from degree two. -/
theorem succ_log_sq_le_four_mul (r : ℕ) (hr : 2 ≤ r) :
    (Nat.log 2 r + 1) ^ 2 ≤ 4 * r := by
  let l := Nat.log 2 r
  have hl : 1 ≤ l := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    exact hr
  have hauxAll : ∀ n : ℕ, (n + 1) ^ 2 ≤ 4 * 2 ^ n := by
    intro n
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num
    · have hn3 : 3 ≤ n := by omega
      exact Nat.le_induction (m := 3)
        (P := fun k _ => (k + 1) ^ 2 ≤ 4 * 2 ^ k)
        (by norm_num)
        (fun k hk ih => by
          calc
            (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
            _ ≤ 2 * (4 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
            _ = 4 * 2 ^ (k + 1) := by rw [pow_succ]; ring)
        n hn3
  have haux : (l + 1) ^ 2 ≤ 4 * 2 ^ l := hauxAll l
  exact haux.trans (Nat.mul_le_mul_left 4
    (Nat.pow_log_le_self 2 (by omega : r ≠ 0)))

/-- Real-cast upper bound for Tracey's rounded permutation generator
ceiling. -/
theorem traceyPermutationGeneratorCeiling_cast_le
    (w : ℕ) (hw : 2 ≤ w) :
    (traceyPermutationGeneratorCeiling w : ℝ) ≤
      (w : ℝ) / Real.sqrt (Real.logb 2 w) + 1 := by
  unfold traceyPermutationGeneratorCeiling
  have hnonneg : 0 ≤ (w : ℝ) / Real.sqrt (Real.logb 2 w) := by
    positivity
  exact (Nat.ceil_lt_add_one hnonneg).le

/-- Explicit coefficient exponent for a primitive affine component of local
degree `r`, transported through `s` actual blocks inside ambient degree `w`.
The first two terms are the elementary-chief cost; the last two are the
linear semisimple constant and its source polynomial. -/
noncomputable def affineComponentCoefficientExponent
    (r s w b : ℕ) : ℝ :=
  let m : ℝ := (Nat.log 2 r + 1 : ℕ) ^ 2
  4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) * m ^ 2 +
    (4 * s * w / Real.sqrt (Real.logb 2 s) +
        s * (traceyPermutationGeneratorCeiling w + 2) + w) * m +
    3 * s * m + 2 * s * m * Real.logb 2 (b + 1)

/-- Uniform two-variable estimate for the explicit affine coefficient.
The first width cost is `o(w²)`; all source-degree dependence is confined to
the final linear logarithmic term. -/
theorem affineComponentCoefficientExponent_le_widthCost
    (r s w b : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (hw : w = r * s) :
    affineComponentCoefficientExponent r s w b ≤
      affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1) := by
  let R : ℝ := r
  let S : ℝ := s
  let X : ℝ := w
  let M : ℝ := (Nat.log 2 r + 1 : ℕ) ^ 2
  let L : ℝ := (Nat.log 2 w + 1 : ℕ) ^ 2
  let qS : ℝ := Real.sqrt (Real.logb 2 S)
  let qW : ℝ := Real.sqrt (Real.logb 2 X)
  let qH : ℝ := Real.sqrt (Real.logb 2 X / 2)
  have hR2 : (2 : ℝ) ≤ R := by simpa [R] using (show (2 : ℝ) ≤ r by exact_mod_cast hr)
  have hS2 : (2 : ℝ) ≤ S := by simpa [S] using (show (2 : ℝ) ≤ s by exact_mod_cast hs)
  have hXeq : X = R * S := by
    simpa [X, R, S] using (show (w : ℝ) = (r : ℝ) * s by exact_mod_cast hw)
  have hX4 : (4 : ℝ) ≤ X := by nlinarith
  have hX0 : 0 ≤ X := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (show 1 ≤ (Nat.log 2 w + 1) ^ 2 by
      have : 1 ≤ Nat.log 2 w + 1 := by omega
      nlinarith)
  have hM4R : M ≤ 4 * R := by
    dsimp [M, R]
    exact_mod_cast succ_log_sq_le_four_mul r hr
  have hrw : r ≤ w := by rw [hw]; nlinarith
  have hlogrw : Nat.log 2 r ≤ Nat.log 2 w := Nat.log_mono_right hrw
  have hML : M ≤ L := by
    dsimp [M, L]
    exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hlogrw 1) 2
  have hqS1 : 1 ≤ qS := by
    apply Real.one_le_sqrt.mpr
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hS2
    simpa [qS, S, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hlog
  have hqW1 : 1 ≤ qW := by
    apply Real.one_le_sqrt.mpr
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ X by linarith)
    simpa [qW, X, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hlog
  have hqHpos : 0 < qH := by
    apply Real.sqrt_pos.2
    exact div_pos (Real.logb_pos (by norm_num) (by linarith)) (by norm_num)
  have hg := traceyPermutationGeneratorCeiling_cast_le w (by omega)
  have hgX : (traceyPermutationGeneratorCeiling w : ℝ) ≤ X / qW + 1 := by
    simpa [X, qW] using hg
  have hlogb0 : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  by_cases hsmall : S ≤ Real.sqrt X
  · have hsSq : S ^ 2 ≤ X := by
      nlinarith [Real.sq_sqrt hX0]
    have hA : 4 * S ^ 2 / qS * M ^ 2 ≤
        4 * X * Real.sqrt X * L ^ 2 := by
      have hqSpos : 0 < qS := lt_of_lt_of_le (by norm_num) hqS1
      have hqSinv : 1 / qS ≤ 1 := (div_le_one hqSpos).2 hqS1
      have hMSq : M ^ 2 ≤ L ^ 2 := by nlinarith
      calc
        4 * S ^ 2 / qS * M ^ 2 =
            (4 * S ^ 2 * M ^ 2) * (1 / qS) := by ring
        _ ≤ (4 * S ^ 2 * M ^ 2) * 1 := by gcongr
        _ ≤ 4 * X * L ^ 2 := by nlinarith
        _ ≤ 4 * X * Real.sqrt X * L ^ 2 := by
          have hsqrt1 : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr (by linarith)
          have hc0 : 0 ≤ 4 * X * L ^ 2 := by positivity
          calc
            4 * X * L ^ 2 = (4 * X * L ^ 2) * 1 := by ring
            _ ≤ (4 * X * L ^ 2) * Real.sqrt X :=
              mul_le_mul_of_nonneg_left hsqrt1 hc0
            _ = _ := by ring
    have hB1 : 4 * S * X / qS * M ≤
        4 * X * Real.sqrt X * L ^ 2 := by
      have hqSpos : 0 < qS := lt_of_lt_of_le (by norm_num) hqS1
      have hqSinv : 1 / qS ≤ 1 := (div_le_one hqSpos).2 hqS1
      have hdiv : 4 * S * X / qS * M ≤ 4 * S * X * M := by
        calc
          _ = (4 * S * X * M) * (1 / qS) := by ring
          _ ≤ (4 * S * X * M) * 1 :=
            mul_le_mul_of_nonneg_left hqSinv (by positivity)
          _ = 4 * S * X * M := by ring
      have hSMsqrt : S * M ≤ Real.sqrt X * L :=
        mul_le_mul hsmall hML hM0 (Real.sqrt_nonneg X)
      calc
        _ ≤ 4 * S * X * M := hdiv
        _ = 4 * X * (S * M) := by ring
        _ ≤ 4 * X * (Real.sqrt X * L) := by gcongr
        _ = 4 * X * Real.sqrt X * L := by ring
        _ ≤ 4 * X * Real.sqrt X * L ^ 2 := by
          have : L ≤ L ^ 2 := by nlinarith
          gcongr
    have hgen : S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) * M ≤
        2 * X * Real.sqrt X * L ^ 2 := by
      have hfrac : X / qW ≤ X := (div_le_self hX0 hqW1)
      have hceil : (traceyPermutationGeneratorCeiling w : ℝ) + 2 ≤ X + 3 := by
        linarith
      have hsqrt1 : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr (by linarith)
      have hXL : X + 3 ≤ 2 * X * L := by nlinarith
      calc
        _ ≤ S * (X + 3) * M := by gcongr
        _ ≤ Real.sqrt X * (2 * X * L) * L := by gcongr
        _ = 2 * X * Real.sqrt X * L ^ 2 := by ring
    have hXM : X * M ≤ X * L := by gcongr
    have hB :
        (4 * S * X / qS +
            S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) + X) * M ≤
          6 * X * Real.sqrt X * L ^ 2 + X * L := by
      calc
        _ = (4 * S * X / qS * M) +
            (S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) * M) +
              X * M := by ring
        _ ≤ (4 * X * Real.sqrt X * L ^ 2) +
            (2 * X * Real.sqrt X * L ^ 2) + X * L :=
          add_le_add (add_le_add hB1 hgen) hXM
        _ = _ := by ring
    have hSM : S * M ≤ 4 * X := by nlinarith
    have hsemi : 3 * S * M ≤ 12 * X := by nlinarith
    have hsemiLog : 2 * S * M * Real.logb 2 (b + 1) ≤
        8 * X * Real.logb 2 (b + 1) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) hlogb0
    have htotal : affineComponentCoefficientExponent r s w b ≤
        10 * X * Real.sqrt X * L ^ 2 + X * L + 12 * X +
          8 * X * Real.logb 2 (b + 1) := by
      dsimp [affineComponentCoefficientExponent, S, X, M, L, qS]
      nlinarith [hA, hB, hsemi, hsemiLog]
    have hF0 : 0 ≤ X * Real.sqrt X * L ^ 2 := by positivity
    have hXL0 : 0 ≤ X * L := by positivity
    have hsmallDom :
        10 * X * Real.sqrt X * L ^ 2 + X * L + 12 * X ≤
          100 * X * Real.sqrt X * L ^ 2 + 100 * X * L := by
      nlinarith [mul_le_mul_of_nonneg_left hL1 hX0]
    have hsecond : 0 ≤ 100 * X ^ 2 / qH := by positivity
    calc
      _ ≤ 10 * X * Real.sqrt X * L ^ 2 + X * L + 12 * X +
          8 * X * Real.logb 2 (b + 1) := htotal
      _ ≤ 100 * X * Real.sqrt X * L ^ 2 + 100 * X * L +
          8 * X * Real.logb 2 (b + 1) := by linarith
      _ ≤ 100 * X * Real.sqrt X * L ^ 2 + 100 * X ^ 2 / qH +
          100 * X * L + 8 * X * Real.logb 2 (b + 1) := by linarith
      _ = _ := by
        simp only [affineComponentWidthCost, X, L, qH]
  · have hSsqrt : Real.sqrt X < S := lt_of_not_ge hsmall
    have hwSsq : X ≤ S ^ 2 := by
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
    have hlog : Real.logb 2 X ≤ 2 * Real.logb 2 S := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by linarith : (0 : ℝ) < X) hwSsq
      simpa [Real.logb_pow] using h
    have hqHS : qH ≤ qS := by
      apply Real.sqrt_le_sqrt
      dsimp [qH, qS]
      linarith
    have hqSpos : 0 < qS := lt_of_lt_of_le (by norm_num) hqS1
    have hdiv : X ^ 2 / qS ≤ X ^ 2 / qH := by
      exact div_le_div_of_nonneg_left (sq_nonneg X) hqHpos hqHS
    have hA : 4 * S ^ 2 / qS * M ^ 2 ≤ 64 * X ^ 2 / qH := by
      have hSM : S * M ≤ 4 * X := by nlinarith
      have hSM0 : 0 ≤ S * M := mul_nonneg (by positivity) hM0
      have h4X0 : 0 ≤ 4 * X := by positivity
      have hsq : (S * M) ^ 2 ≤ (4 * X) ^ 2 :=
        sq_le_sq₀ hSM0 h4X0 |>.2 hSM
      have hnum : 4 * (S * M) ^ 2 ≤ 64 * X ^ 2 := by nlinarith
      calc
        4 * S ^ 2 / qS * M ^ 2 = 4 * (S * M) ^ 2 / qS := by ring
        _ ≤ 64 * X ^ 2 / qS := by
          exact div_le_div_of_nonneg_right hnum hqSpos.le
        _ ≤ 64 * X ^ 2 / qH := by gcongr
    have hB1 : 4 * S * X / qS * M ≤ 16 * X ^ 2 / qH := by
      have hSM : S * M ≤ 4 * X := by nlinarith
      have hnum : 4 * X * (S * M) ≤ 16 * X ^ 2 := by nlinarith
      calc
        4 * S * X / qS * M = 4 * X * (S * M) / qS := by ring
        _ ≤ 16 * X ^ 2 / qS := by
          exact div_le_div_of_nonneg_right hnum hqSpos.le
        _ ≤ 16 * X ^ 2 / qH := by gcongr
    have hqHW : qH ≤ qW := by
      apply Real.sqrt_le_sqrt
      dsimp [qH, qW]
      have : 0 ≤ Real.logb 2 X := (Real.logb_pos (by norm_num) (by linarith)).le
      linarith
    have hgen : S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) * M ≤
        4 * X ^ 2 / qH + 12 * X := by
      have hSM : S * M ≤ 4 * X := by nlinarith
      have hqWpos : 0 < qW := lt_of_lt_of_le hqHpos hqHW
      have hfrac : X / qW ≤ X / qH := by
        exact div_le_div_of_nonneg_left hX0 hqHpos hqHW
      have hgenCeil : (traceyPermutationGeneratorCeiling w : ℝ) + 2 ≤
          X / qW + 3 := by linarith
      have hprod :
          (S * M) * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) ≤
            (4 * X) * (X / qW + 3) := by
        exact mul_le_mul hSM hgenCeil (by positivity) (by positivity)
      calc
        S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) * M =
            (S * M) * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) := by ring
        _ ≤ (4 * X) * (X / qW + 3) := hprod
        _ ≤ (4 * X) * (X / qH + 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * X ^ 2 / qH + 12 * X := by ring
    have hXM : X * M ≤ X * L := by gcongr
    have hB :
        (4 * S * X / qS +
            S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) + X) * M ≤
          20 * X ^ 2 / qH + 12 * X + X * L := by
      calc
        _ = (4 * S * X / qS * M) +
            (S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) * M) +
              X * M := by ring
        _ ≤ (16 * X ^ 2 / qH) +
            (4 * X ^ 2 / qH + 12 * X) + X * L :=
          add_le_add (add_le_add hB1 hgen) hXM
        _ = _ := by ring
    have hSM : S * M ≤ 4 * X := by nlinarith
    have hsemi : 3 * S * M ≤ 12 * X := by nlinarith
    have hsemiLog : 2 * S * M * Real.logb 2 (b + 1) ≤
        8 * X * Real.logb 2 (b + 1) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) hlogb0
    have htotal : affineComponentCoefficientExponent r s w b ≤
        84 * X ^ 2 / qH + 24 * X + X * L +
          8 * X * Real.logb 2 (b + 1) := by
      change 4 * S ^ 2 / qS * M ^ 2 +
          (4 * S * X / qS +
            S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) + X) * M +
          3 * S * M + 2 * S * M * Real.logb 2 (b + 1) ≤ _
      calc
        _ = (4 * S ^ 2 / qS * M ^ 2 +
              (4 * S * X / qS +
                S * ((traceyPermutationGeneratorCeiling w : ℝ) + 2) + X) * M) +
            (3 * S * M + 2 * S * M * Real.logb 2 (b + 1)) := by ring
        _ ≤ (64 * X ^ 2 / qH +
              (20 * X ^ 2 / qH + 12 * X + X * L) +
            (12 * X + 8 * X * Real.logb 2 (b + 1))) :=
          add_le_add (add_le_add hA hB) (add_le_add hsemi hsemiLog)
        _ = _ := by ring
    have hQ0 : 0 ≤ X ^ 2 / qH := by positivity
    have hXL0 : 0 ≤ X * L := by positivity
    have hlargeDom : 84 * X ^ 2 / qH + 24 * X + X * L ≤
        100 * X ^ 2 / qH + 100 * X * L := by
      have hXleXL : X ≤ X * L := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hX0
      have hQ : 84 * (X ^ 2 / qH) ≤ 100 * (X ^ 2 / qH) := by
        nlinarith
      have hlin : 24 * X + X * L ≤ 100 * (X * L) := by
        nlinarith
      calc
        _ = 84 * (X ^ 2 / qH) + (24 * X + X * L) := by ring
        _ ≤ 100 * (X ^ 2 / qH) + 100 * (X * L) :=
          add_le_add hQ hlin
        _ = _ := by ring
    have hfirst : 0 ≤ 100 * X * Real.sqrt X * L ^ 2 := by positivity
    calc
      _ ≤ 84 * X ^ 2 / qH + 24 * X + X * L +
          8 * X * Real.logb 2 (b + 1) := htotal
      _ ≤ 100 * X ^ 2 / qH + 100 * X * L +
          8 * X * Real.logb 2 (b + 1) := by linarith
      _ ≤ 100 * X * Real.sqrt X * L ^ 2 + 100 * X ^ 2 / qH +
          100 * X * L + 8 * X * Real.logb 2 (b + 1) := by linarith
      _ = _ := by
        simp only [affineComponentWidthCost, X, L, qH]

namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

include P

/-- The logarithm of the literal component order is at most the square of
one plus the binary logarithm of the literal block degree. -/
theorem component_logb_card_le_logSquare :
    Real.logb 2 (Nat.card block.Component) ≤
      ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 := by
  let x : block.Fibre := ⟨basePoint, block.map_base⟩
  let r := Nat.card block.Fibre
  let l := Nat.log 2 r
  have hrUpper : r ≤ 2 ^ (l + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r).le
  have hcard : Nat.card block.Component ≤
      2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) := by
    calc
      Nat.card block.Component ≤ Nat.card block.Fibre *
          Nat.card block.Fibre ^ Nat.log 2 (Nat.card block.Fibre) :=
        P.card_le_domain_pow_log x
      _ = r ^ (l + 1) := by simp [r, l, pow_succ']
      _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hrUpper _
      _ = 2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) := by
        dsimp [l, r]
        rw [pow_two, pow_mul]
  have hposR : (0 : ℝ) < Nat.card block.Component := by
    exact_mod_cast Nat.card_pos (α := block.Component)
  have hcardR : (Nat.card block.Component : ℝ) ≤
      (2 ^ ((Nat.log 2 (Nat.card block.Fibre) + 1) ^ 2) : ℕ) := by
    exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hposR hcardR
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), one_mul, mul_one,
    Nat.cast_add, Nat.cast_one] using hlog

/-- Both retained tower budgets are bounded by the same literal local-order
budget. -/
theorem tower_logBudgets_le_logSquare :
    let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    T.elementaryLogBudget ≤
        ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 ∧
      T.semisimpleLogBudget ≤
        ((Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) : ℝ) ^ 2 := by
  let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  have hsum := T.elementaryLogBudget_add_semisimpleLogBudget_eq_card
  change T.elementaryLogBudget + T.semisimpleLogBudget =
    Real.logb 2 (Nat.card block.Component) at hsum
  have he0 := T.elementaryLogBudget_nonneg
  have hs0 := T.semisimpleLogBudget_nonneg
  have htotal := component_logb_card_le_logSquare block P
  constructor <;> nlinarith

/-- The actual local-chief coefficient is bounded by the explicit affine
component exponent.  This is the construction-level estimate later summed
over the growing owner menu. -/
theorem tower_coefficient_le_explicit
    (hgen : FiniteSimpleTwoGeneratorBound) (b : ℕ) :
    let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    T.envelope.coefficient b ≤
      (2 : ℝ) ^ affineComponentCoefficientExponent
        (Nat.card block.Fibre) (Nat.card block.Points) w b := by
  let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  let m : ℝ := (Nat.log 2 (Nat.card block.Fibre) + 1 : ℕ) ^ 2
  obtain ⟨he, hs⟩ := tower_logBudgets_le_logSquare
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  have he0 := T.elementaryLogBudget_nonneg
  have hs0 := T.semisimpleLogBudget_nonneg
  have hm0 : 0 ≤ m := by positivity
  have hsBlocks : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hraw := T.envelope_coefficient_le_two_rpow_linearSemisimpleBudget
    hgen hsBlocks b
  have hraw' : T.envelope.coefficient b ≤ (2 : ℝ) ^
        (4 * (Nat.card block.Points : ℝ) ^ 2 /
              Real.sqrt (Real.logb 2 (Nat.card block.Points)) *
                T.elementaryLogBudget ^ 2 +
          (4 * Nat.card block.Points * w /
                Real.sqrt (Real.logb 2 (Nat.card block.Points)) +
              Nat.card block.Points *
                (traceyPermutationGeneratorCeiling w + 2) + w) *
            T.elementaryLogBudget +
          3 * Nat.card block.Points * T.semisimpleLogBudget +
          2 * Nat.card block.Points * T.semisimpleLogBudget *
            Real.logb 2 (b + 1)) := by
    simpa only [Fintype.card_eq_nat_card, initialState] using hraw
  refine hraw'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have hsqrt : 0 < Real.sqrt (Real.logb 2 (Nat.card block.Points)) :=
    Real.sqrt_pos.2 (Real.logb_pos (by norm_num)
      (by exact_mod_cast block.degrees_ge_two.2))
  have hA0 : 0 ≤ 4 * (Nat.card block.Points : ℝ) ^ 2 /
      Real.sqrt (Real.logb 2 (Nat.card block.Points)) := by positivity
  have hB0 : 0 ≤ 4 * (Nat.card block.Points : ℝ) * w /
        Real.sqrt (Real.logb 2 (Nat.card block.Points)) +
      Nat.card block.Points * (traceyPermutationGeneratorCeiling w + 2) + w := by
    positivity
  have hlog0 : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  have heSq : T.elementaryLogBudget ^ 2 ≤ m ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left heSq hA0
  have h2 := mul_le_mul_of_nonneg_left he hB0
  have h3 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 3 * (Nat.card block.Points : ℝ) by positivity)
  have h4 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * (Nat.card block.Points : ℝ) *
      Real.logb 2 (b + 1) by positivity)
  dsimp [affineComponentCoefficientExponent, m]
  nlinarith

variable (S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)

/-- The finite coefficient is a theorem of the literal affine tower.  Its
width-only part is the standard subquadratic cost used by the global menu. -/
theorem coefficient_bound
    (hgen : FiniteSimpleTwoGeneratorBound) (b : ℕ) :
    (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).coefficient b ≤
      (2 : ℝ) ^
        (affineComponentWidthCost w +
          8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  have hraw := tower_coefficient_le_explicit
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hgen b
  have hexp := affineComponentCoefficientExponent_le_widthCost
    (Nat.card block.Fibre) (Nat.card block.Points) w b
    block.degrees_ge_two.1 block.degrees_ge_two.2 (width_eq block)
  exact hraw.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

/-- The source margin plus the coefficient theorem give the exact
construction-facing record required by the affine-aware catalogue bridge. -/
noncomputable def preE7Margin
    (hgen : FiniteSimpleTwoGeneratorBound) :
    RelativeCompleteSourceEnvelope.PreE7Margin
      (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P) where
  eta_nonneg := by
    simpa only [envelope, tower] using
      ActualWreathCompressionTower.envelope_eta_nonneg
        (tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)
  seedDegree_two_le := by
    rw [envelope, ActualWreathCompressionTower.envelope_v]
    simpa using block.degrees_ge_two.2
  margin := by
    simpa only [envelope, tower, trace, capacity] using S.margin
  coefficient_bound := coefficient_bound
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hgen

/-- **Imprimitive affine-component transfer.**  The component-native margin
is transported through the actual block system; the complete coefficient
and its subquadratic menu growth are proved rather than assumed. -/
noncomputable def toAmbientSource
    (hgen : FiniteSimpleTwoGeneratorBound) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P)
      (preE7Margin hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P S hgen)

end ComponentSource

/-- Function spelling used by the primitive-catalogue consumer assembly. -/
noncomputable def imprimitiveAffineComponentTransfer
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : FiniteSimpleTwoGeneratorBound)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  ComponentSource.toAmbientSource
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P S hgen

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
