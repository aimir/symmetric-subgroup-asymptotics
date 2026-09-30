import SymmetricSubgroupAsymptotics.Non2PreE7Sns2Menu
import SymmetricSubgroupAsymptotics.GrowingQuotientSecondaryForwardEstimate

/-!
# The all-width SNS2 cold forward row

The quotient normal-subgroup count has a real quarter-square cost in its
binary logarithmic order.  It is retained in the same exponent as the
physical Gaussian reserve.  Only the normalized remainder is passed to the
subexponential menu-mass interface.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem sns2_cold_entry_le {w : ℕ} (i : PreE7Sns2MenuIndex w)
    (b : ℕ) :
    fusionWidthColdKernel b w (preE7Sns2MenuCoefficient i b)
        (preE7Sns2MenuNormalizer i) (preE7Sns2MenuSlope i) ≤
      (eulerProduct⁻¹ ^ 2 * (((b + w + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (preE7Sns2NormalizedCoefficient i b /
            preE7Sns2MenuNormalizer i)) *
        (2 : ℝ) ^ (-(w : ℝ) * b / 80 - (w : ℝ) ^ 2 / 80 + 2) := by
  let C := preE7Sns2MenuCertificate i
  let l := C.quotientRank
  let r := halfDegree w
  have hkernel := fusionWidthColdKernel_quadratic_le b w
    (preE7Sns2MenuCoefficient_nonneg i b)
    (preE7Sns2MenuNormalizer_pos i)
    (α := preE7Sns2MenuSlope i)
  have hgap := sns2_halfDegree_cold_main_gap
    (C.width_lower) (C.quotientRank_le) (b := b)
  have hexp :
      -(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 +
          (preE7Sns2MenuSlope i) * b + (l : ℝ) ^ 2 / 4 ≤
        -(w : ℝ) * b / 80 - (w : ℝ) ^ 2 / 80 + 2 := by
    dsimp [preE7Sns2MenuSlope, C, l, r] at hgap ⊢
    have hr0 : (0 : ℝ) ≤ halfDegree w := by positivity
    linarith
  apply hkernel.trans
  rw [preE7Sns2MenuCoefficient_eq_normalized]
  let E : ℝ := -(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 +
    (preE7Sns2MenuSlope i) * b + (l : ℝ) ^ 2 / 4
  have hpow : (2 : ℝ) ^ E ≤
      (2 : ℝ) ^ (-(w : ℝ) * b / 80 - (w : ℝ) ^ 2 / 80 + 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have heq :
      (eulerProduct⁻¹ ^ 2 * (((b + w + 1 : ℕ) : ℝ) ^ (w + 2)) *
          ((preE7Sns2NormalizedCoefficient i b *
              (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4)) /
            preE7Sns2MenuNormalizer i)) *
        (2 : ℝ) ^
          (-(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 +
            (r : ℝ) / 4 + 1 / 4 +
            preE7Sns2MenuSlope i * b) =
      (eulerProduct⁻¹ ^ 2 * (((b + w + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((r : ℝ) / 4 + 1 / 4) *
          (preE7Sns2NormalizedCoefficient i b /
            preE7Sns2MenuNormalizer i)) * (2 : ℝ) ^ E := by
    let E₀ : ℝ := -(r : ℝ) * b / 4 - r ^ 2 / 4 +
      preE7Sns2MenuSlope i * b
    have hfull :
        (2 : ℝ) ^
            (-(r : ℝ) * b / 4 - r ^ 2 / 4 + r / 4 + 1 / 4 +
              preE7Sns2MenuSlope i * b) =
          (2 : ℝ) ^ ((r : ℝ) / 4 + 1 / 4) * (2 : ℝ) ^ E₀ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E₀]
      ring
    have hmerge :
        (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4) * (2 : ℝ) ^ E₀ =
          (2 : ℝ) ^ E := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [E, E₀]
      ring
    rw [hfull, div_eq_mul_inv]
    rw [← hmerge]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hpow (mul_nonneg
    (mul_nonneg
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr euler_positive.le) 2)
        (by positivity)) (by positivity))
    (div_nonneg (preE7Sns2NormalizedCoefficient_nonneg i b)
      (preE7Sns2MenuNormalizer_pos i).le))

/-- Once the normalized menu overhead is absorbed, every SNS2 width loses
at least `w*n/100`. -/
theorem preE7Sns2ColdWidthSum_le
    (hmass : PreE7Sns2NormalizedMenuMassBound) :
    ∀ᶠ n : ℕ in atTop, ∀ w, w ∈ Finset.Ico 5 (n + 1) →
      growingQuotientColdWidthSum (n - w) w
          (fun i => preE7Sns2MenuCoefficient (w := w) i)
          (fun i => preE7Sns2MenuNormalizer (w := w) i)
          (fun i => preE7Sns2MenuSlope (w := w) i) ≤
        (2 : ℝ) ^ (-(w : ℝ) * n / 100) := by
  have hoverhead := growingMenuMass_cold_overhead
    (ι := PreE7Sns2MenuIndex) 5
    (fun w i => preE7Sns2NormalizedCoefficient (w := w) i)
    (fun w i => preE7Sns2MenuNormalizer (w := w) i)
    (show (0 : ℝ) < 1 / 100 by norm_num) (by omega)
    (fun w i b => preE7Sns2NormalizedCoefficient_nonneg i b)
    (fun w i => preE7Sns2MenuNormalizer_pos i) hmass
  filter_upwards [hoverhead, eventually_ge_atTop 214] with n hover hn
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hnadd : n - w + w = n := Nat.sub_add_cancel hwn
  have hentry (i : PreE7Sns2MenuIndex w) :=
    sns2_cold_entry_le i (n - w)
  have hsum :
      growingQuotientColdWidthSum (n - w) w
          (fun i => preE7Sns2MenuCoefficient (w := w) i)
          (fun i => preE7Sns2MenuNormalizer (w := w) i)
          (fun i => preE7Sns2MenuSlope (w := w) i) ≤
        (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
            (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
            (∑ i : PreE7Sns2MenuIndex w,
              preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
          (2 : ℝ) ^
            (-(w : ℝ) * (n - w) / 80 - (w : ℝ) ^ 2 / 80 + 2) := by
    unfold growingQuotientColdWidthSum
    calc
      _ ≤ ∑ i : PreE7Sns2MenuIndex w,
          (eulerProduct⁻¹ ^ 2 * (((n - w + w + 1 : ℕ) : ℝ) ^ (w + 2)) *
              (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
              (preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
            (2 : ℝ) ^
              (-(w : ℝ) * (n - w) / 80 - (w : ℝ) ^ 2 / 80 + 2) :=
        Finset.sum_le_sum (fun i _ => by
          simpa only [Nat.cast_sub hwn] using hentry i)
      _ = _ := by
        rw [hnadd]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hover := hover w hw
  have hmain :
      (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (∑ i : PreE7Sns2MenuIndex w,
            preE7Sns2NormalizedCoefficient i (n - w) /
              preE7Sns2MenuNormalizer i)) *
        (2 : ℝ) ^
          (-(w : ℝ) * ((n : ℝ) - w) / 80 - (w : ℝ) ^ 2 / 80 + 2) ≤
      (2 : ℝ) ^ ((1 / 100 : ℝ) * w * n / 16) *
        (2 : ℝ) ^
          (-(w : ℝ) * ((n : ℝ) - w) / 80 - (w : ℝ) ^ 2 / 80 + 2) :=
    mul_le_mul_of_nonneg_right hover (by positivity)
  apply hsum.trans
  calc
    _ ≤ (2 : ℝ) ^ ((1 / 100 : ℝ) * w * n / 16) *
        (2 : ℝ) ^
          (-(w : ℝ) * (n - w) / 80 - (w : ℝ) ^ 2 / 80 + 2) := hmain
    _ = (2 : ℝ) ^
        ((1 / 100 : ℝ) * w * n / 16 +
          (-(w : ℝ) * (n - w) / 80 - (w : ℝ) ^ 2 / 80 + 2)) := by
      exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hwnR : (0 : ℝ) ≤ w * n := by positivity
      have hlarge : (3200 : ℝ) ≤ 3 * w * n := by
        have hw5 : (5 : ℝ) ≤ w := by exact_mod_cast hww.1
        have hn214 : (214 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      nlinarith)

/-- The complete SNS2 cold row is an exponentially contractive forward
estimate, uniformly over all removed widths. -/
noncomputable def preE7Sns2Cold_exponentialForwardEstimate
    (hmass : PreE7Sns2NormalizedMenuMassBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (fun n => ∑ b ∈ Finset.range n,
        growingQuotientColdRow 5
          (fun w i => preE7Sns2MenuCoefficient (w := w) i)
          (fun w i => preE7Sns2MenuNormalizer (w := w) i)
          (fun w i => preE7Sns2MenuSlope (w := w) i) n b *
            ordinarySubgroupRatio b) := by
  let hwitness := eventually_atTop.mp (preE7Sns2ColdWidthSum_le hmass)
  let N := max 214 (Classical.choose hwitness)
  have hN := Classical.choose_spec hwitness
  let kernel := growingQuotientColdRow 5
    (fun w i => preE7Sns2MenuCoefficient (w := w) i)
    (fun w i => preE7Sns2MenuNormalizer (w := w) i)
    (fun w i => preE7Sns2MenuSlope (w := w) i)
  refine
    { scalar := fun _ => 0
      kernel := kernel
      threshold := N
      rate := 1 / 20
      scalarConst := 1
      rowConst := 2
      rate_pos := by norm_num
      scalarConst_pos := by norm_num
      rowConst_nonneg := by norm_num
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact growingQuotientColdRow_nonneg 5 _ _ _
      (fun w i b => preE7Sns2MenuCoefficient_nonneg i b)
      (fun w i => preE7Sns2MenuNormalizer_pos i) n b
  · intro n _
    simp [kernel]
  · intro n _
    positivity
  · intro n hn
    have hn214 : 214 ≤ n := (le_max_left _ _).trans hn
    have hnW : Classical.choose hwitness ≤ n :=
      (le_max_right _ _).trans hn
    have hwidth := hN n hnW
    let x : ℝ := (2 : ℝ) ^ (-(n : ℝ) / 100)
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      calc
        (2 : ℝ) ^ (-(n : ℝ) / 100) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have hnR : (100 : ℝ) ≤ n := by exact_mod_cast (by omega : 100 ≤ n)
            linarith)
        _ = 1 / 2 := by norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hx1 : x < 1 := hxhalf.trans_lt (by norm_num)
    have htotal : growingQuotientColdTotal 5 n
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) ≤
      ∑ w ∈ Finset.Ico 5 (n + 1), x ^ w := by
      unfold growingQuotientColdTotal
      apply Finset.sum_le_sum
      intro w hw
      calc
        _ ≤ (2 : ℝ) ^ (-(w : ℝ) * n / 100) := hwidth w hw
        _ = x ^ w := by
          dsimp [x]
          rw [← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
    have hgeom := geom_sum_Ico_le_of_lt_one
      (x := x) (m := 5) (n := n + 1) hx0 hx1
    have hden : (1 - x)⁻¹ ≤ 2 := by
      have hhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
      have hpos : 0 < 1 - x := sub_pos.mpr hx1
      rw [inv_le_iff_one_le_mul₀' hpos]
      nlinarith
    rw [growingQuotientColdRow_sum 5 (by omega) _ _ _ n]
    calc
      _ ≤ ∑ w ∈ Finset.Ico 5 (n + 1), x ^ w := htotal
      _ ≤ x ^ 5 / (1 - x) := hgeom
      _ = x ^ 5 * (1 - x)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ x ^ 5 * 2 := mul_le_mul_of_nonneg_left hden (pow_nonneg hx0 _)
      _ = 2 * (2 : ℝ) ^ (-(1 / 20 : ℝ) * n) := by
        dsimp [x]
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring_nf

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
