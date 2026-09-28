import SymmetricSubgroupAsymptotics.FusionWidthUniformNormalization
import SymmetricSubgroupAsymptotics.FusionCompleteQuotientTransfer
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-!
# Uniform hot kernel for a growing complete comparator

This file combines the exact rounded-moment square with the arbitrary-width
hot denominator.  The conclusion retains the original action divisor and an
arbitrary nonnegative certificate weight.  It is pointwise in the complement
degree, removed width, and comparator degree, so a later theorem can sum a
growing menu without first freezing any of those parameters.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The actual target degree of the simultaneous quotient graph selected by
the rounded growing moment. -/
def growingQuotientGraphDegree (δ : ℝ) (b v : ℕ) : ℕ :=
  b + growingQuotientMoment δ (v : ℝ) (b : ℝ) * v

/-- The exponential threshold used for the hot/cold split. -/
def growingQuotientThreshold (c : ℝ) (b : ℕ) : ℝ :=
  (2 : ℝ) ^ (c * b)

theorem growingQuotientThreshold_pos (c : ℝ) (b : ℕ) :
    0 < growingQuotientThreshold c b := by
  unfold growingQuotientThreshold
  positivity

theorem growingQuotientThreshold_pow (c : ℝ) (b q : ℕ) (hq : 1 ≤ q) :
    growingQuotientThreshold c b ^ (q - 1) =
      (2 : ℝ) ^ (((q : ℝ) - 1) * c * b) := by
  unfold growingQuotientThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [Nat.cast_sub hq, Nat.cast_one]
  ring

/-- The original factorial pointing divided by the original action divisor,
before the local hot/cold terms are installed. -/
def growingQuotientNormalizedPointing (b w : ℕ) (A : ℝ) : ℝ :=
  ((((b + w).factorial : ℝ) / (b.factorial : ℝ)) / A) /
    exactBenchmark (b + w)

/-- Benchmark-normalized hot contribution for one original action.  `D/A`
is the retained certificate weight divided by the original action divisor;
`η` is the lift slope and `c` is the splitting threshold exponent. -/
def growingQuotientHotKernel (s : ℕ → ℝ) (b w v : ℕ)
    (D A η δ c : ℝ) : ℝ :=
  ((((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
      exactBenchmark (b + w)) * (D / A) *
    (2 : ℝ) ^ (η * b -
      ((growingQuotientMoment δ (v : ℝ) (b : ℝ) : ℝ) - 1) * c * b) *
    s (growingQuotientGraphDegree δ b v)

/-- Exact hot normalization at the rounded complete-quotient moment. -/
theorem growingQuotient_hot_identity (s : ℕ → ℝ) (b w v : ℕ)
    (D A η δ c : ℝ) :
    growingQuotientNormalizedPointing b w A *
        (D * (2 : ℝ) ^ (η * b) /
            growingQuotientThreshold c b ^
              (growingQuotientMoment δ (v : ℝ) (b : ℝ) - 1) *
          s (growingQuotientGraphDegree δ b v)) =
      growingQuotientHotKernel s b w v D A η δ c := by
  rw [growingQuotientThreshold_pow c b _
    (growingQuotientMoment_pos δ (v : ℝ) (b : ℝ))]
  unfold growingQuotientNormalizedPointing growingQuotientHotKernel
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  ring

/-- Exact cold normalization, including the benchmark ratio at the unchanged
complement degree. -/
theorem growingQuotient_cold_identity (s : ℝ) (b w : ℕ)
    (D A η c : ℝ) :
    growingQuotientNormalizedPointing b w A *
        (s * D * (2 : ℝ) ^ (η * b) * growingQuotientThreshold c b) =
      fusionWidthColdKernel b w D A (η + c) * (s / exactBenchmark b) := by
  have hb := ne_of_gt (exactBenchmark_pos b)
  unfold growingQuotientNormalizedPointing growingQuotientThreshold
    fusionWidthColdKernel fusionWidthPointingRatio
  have hp : (2 : ℝ) ^ (η * b) * (2 : ℝ) ^ (c * b) =
      (2 : ℝ) ^ ((η + c) * b) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [show s * D * (2 : ℝ) ^ (η * b) * (2 : ℝ) ^ (c * b) =
    s * D * ((2 : ℝ) ^ (η * b) * (2 : ℝ) ^ (c * b)) by ring, hp]
  field_simp

theorem growingQuotientHotKernel_nonneg (s : ℕ → ℝ) (b w v : ℕ)
    {D A η δ c : ℝ} (hs : 0 ≤ s (growingQuotientGraphDegree δ b v))
    (hD : 0 ≤ D) (hA : 0 < A) :
    0 ≤ growingQuotientHotKernel s b w v D A η δ c := by
  unfold growingQuotientHotKernel
  have hbench := exactBenchmark_pos (b + w)
  positivity

/-- The whole-axis physical quotient transfer, installed exactly into one
growing hot scalar and one cold forward coefficient.  The normalizer of the
original action is used in both kernels. -/
theorem fusionPhysical_growingQuotient_kernel_bound
    {R : Type*} [Group R] [Finite R] {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (ρR : R →* Equiv.Perm (Fin v)) (hρR : Function.Injective ρR)
    (D η δ c : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        (D * (2 : ℝ) ^ (η * b)) * completeQuotientWeight (R := R) J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ)) b w v D
          (Nat.card
            (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          η δ c +
        fusionWidthColdKernel b w D
          (Nat.card
            (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (η + c) * ((subgroupCount b : ℝ) / exactBenchmark b) := by
  let q := growingQuotientMoment δ (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  have hq : 1 ≤ q := growingQuotientMoment_pos δ (v : ℝ) (b : ℝ)
  have hfactor : 0 ≤ D * (2 : ℝ) ^ (η * b) := mul_nonneg hD (by positivity)
  have ht := growingQuotientThreshold_pos c b
  have hbound := fusionPhysical_completeQuotient_normalized_bound
    U P hP ρR hρR (D * (2 : ℝ) ^ (η * b))
      (growingQuotientThreshold c b) hfactor ht hq henvelope
  change _ ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ)) b w v D A η δ c +
      fusionWidthColdKernel b w D A (η + c) *
        ((subgroupCount b : ℝ) / exactBenchmark b)
  calc
    _ ≤ growingQuotientNormalizedPointing b w A *
        (D * (2 : ℝ) ^ (η * b) /
            growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * (2 : ℝ) ^ (η * b) *
            growingQuotientThreshold c b) := by
      simpa only [q, A, growingQuotientNormalizedPointing,
        div_eq_mul_inv, mul_assoc] using hbound
    _ = growingQuotientNormalizedPointing b w A *
          (D * (2 : ℝ) ^ (η * b) /
              growingQuotientThreshold c b ^ (q - 1) *
                (subgroupCount (b + q * v) : ℝ)) +
        growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * D * (2 : ℝ) ^ (η * b) *
            growingQuotientThreshold c b) := by ring
    _ = _ := by
      congr 1
      · simpa only [q, growingQuotientGraphDegree] using
          growingQuotient_hot_identity
            (fun n => (subgroupCount n : ℝ)) b w v D A η δ c
      · exact growingQuotient_cold_identity (subgroupCount b : ℝ)
          b w D A η c

/-- The complete pointwise hot estimate.  Its only input about the unknown
count sequence is the displayed coarse bound at the one graph degree used by
the moment.  All main quadratic terms are discharged by
`growingQuotient_hot_exponent_le`; the remaining linear normalization and
coarse-error terms are explicit for later uniform aggregation. -/
theorem growingQuotientHotKernel_le
    (s : ℕ → ℝ) (b w v : ℕ) {D A ρ δ η c ε : ℝ}
    (hD : 0 ≤ D) (hA : 0 < A)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hδ : 0 ≤ δ) (hv : 0 < v)
    (hratio : ρ / 2 ≤ δ / (v : ℝ))
    (hvupper : (v : ℝ) ≤ (1 - 4 * ρ) * w)
    (hδlower : ρ * w / 2 ≤ δ)
    (hmargin : η + c - w / 8 ≤ -δ / 2)
    (hc : c = (v : ℝ) / 8 + δ / 2)
    (hs : s (growingQuotientGraphDegree δ b v) ≤
      (2 : ℝ) ^ ((1 / 16 + ε) *
        (growingQuotientGraphDegree δ b v : ℝ) ^ 2)) :
    growingQuotientHotKernel s b w v D A η δ c ≤
      eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) * (D / A) *
        (2 : ℝ) ^ (-(ρ ^ 2) * ((b + w : ℕ) : ℝ) ^ 2 / 4 +
          ε * (growingQuotientGraphDegree δ b v : ℝ) ^ 2 +
          5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) := by
  let q := growingQuotientMoment δ (v : ℝ) (b : ℝ)
  let M := growingQuotientGraphDegree δ b v
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hmain := growingQuotient_hot_exponent_le
    (ρ := ρ) (δ := δ) (v := (v : ℝ)) (b := (b : ℝ)) (w := (w : ℝ))
    (η := η) (a := c) hρ hρ8 hδ (by positivity) (by positivity) hvR
    hratio hvupper hδlower hmargin hc
  have hdegree : (M : ℝ) = (b : ℝ) + (q : ℝ) * (v : ℝ) := by
    dsimp [M, growingQuotientGraphDegree, q]
    push_cast
    ring
  have hexp :
      -((b + w : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4 +
          (η * b - ((q : ℝ) - 1) * c * b) +
          (1 / 16 + ε) * (M : ℝ) ^ 2 ≤
        -(ρ ^ 2) * ((b + w : ℕ) : ℝ) ^ 2 / 4 +
          ε * (M : ℝ) ^ 2 + 5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4 := by
    rw [hdegree]
    push_cast at hmain ⊢
    nlinarith
  unfold growingQuotientHotKernel
  change
    ((((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
        exactBenchmark (b + w)) * (D / A) *
      (2 : ℝ) ^ (η * b - ((q : ℝ) - 1) * c * b) * s M ≤ _
  calc
    _ ≤ (((((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
          exactBenchmark (b + w)) * (D / A) *
        (2 : ℝ) ^ (η * b - ((q : ℝ) - 1) * c * b)) *
          (2 : ℝ) ^ ((1 / 16 + ε) * (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (by
        have hbench := exactBenchmark_pos (b + w)
        positivity)
    _ ≤ (eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) *
          (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4)) * (D / A) *
        (2 : ℝ) ^ (η * b - ((q : ℝ) - 1) * c * b) *
        (2 : ℝ) ^ ((1 / 16 + ε) * (M : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (fusionWidthHot_pointing_denominator_le b w)
            (div_nonneg hD hA.le)) (by positivity)) (by positivity)
    _ = eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) * (D / A) *
        (2 : ℝ) ^
          (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4 +
            (η * b - ((q : ℝ) - 1) * c * b) +
            (1 / 16 + ε) * (M : ℝ) ^ 2) := by
      have hm (x y z C E : ℝ) :
          (C * (2 : ℝ) ^ x) * E * (2 : ℝ) ^ y * (2 : ℝ) ^ z =
            (C * E) * (2 : ℝ) ^ (x + y + z) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring
      exact hm _ _ _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity))
        (div_nonneg hD hA.le))

end SymmetricSubgroupAsymptotics

end
