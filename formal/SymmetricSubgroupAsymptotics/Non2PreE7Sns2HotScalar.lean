import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ColdForward

/-!
# The all-width SNS2 hot scalar

The weighted binary rank tail has two regimes.  When the quotient rank is at
most `⌈b/100⌉`, square completion retains a `b²/40000` deficit.  Otherwise
the constraint `3ℓ ≤ w` makes the removed width a fixed fraction of the
ambient degree and gives a stronger deficit.  This file sums both regimes in
one literal original-weight menu, with the quarter-square normal-subgroup cost
kept inside the exponent until the final aggregation.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem fusionCoarse_global_constant
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      (subgroupCount m : ℝ) ≤
        K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (m : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoarse epsilon hepsilon)
  let K : ℝ := 1 + ∑ m ∈ Finset.range N, (subgroupCount m : ℝ)
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range N, (subgroupCount m : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hK1 : (1 : ℝ) ≤ K := by dsimp [K]; linarith
  refine ⟨K, lt_of_lt_of_le (by norm_num) hK1, ?_⟩
  intro m
  have hexp0 : 0 ≤ (1 / 16 + epsilon) * (m : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hpow1 : (1 : ℝ) ≤
      (2 : ℝ) ^ ((1 / 16 + epsilon) * (m : ℝ) ^ 2) := by
    exact Real.one_le_rpow (by norm_num) hexp0
  by_cases hm : N ≤ m
  · exact (hN m hm).trans
      (le_mul_of_one_le_left (by positivity) hK1)
  · have hmmem : m ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hsingle : (subgroupCount m : ℝ) ≤
        ∑ k ∈ Finset.range N, (subgroupCount k : ℝ) := by
      exact Finset.single_le_sum
        (f := fun k : ℕ => (subgroupCount k : ℝ))
        (fun k hk => by positivity) hmmem
    calc
      (subgroupCount m : ℝ) ≤
          ∑ k ∈ Finset.range N, (subgroupCount k : ℝ) := hsingle
      _ ≤ K := by dsimp [K]; linarith
      _ ≤ K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (m : ℝ) ^ 2) :=
        le_mul_of_one_le_right (le_trans (by norm_num) hK1) hpow1

private theorem sns2_tilt_le_ambient {n w : ℕ} (hw : w ≤ n)
    (l : ℕ) (hl : 3 * l ≤ w) :
    sns2RankTailTilt (n - w) l ≤ n := by
  have hlw : l ≤ w := by omega
  have htilt : rankTail51Tilt (n - w) ≤ n - w := by
    unfold rankTail51Tilt
    omega
  unfold sns2RankTailTilt
  exact max_le (hlw.trans hw) (htilt.trans (Nat.sub_le _ _))

private theorem sns2_hot_entry_le
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ w,
      w ∈ Finset.Ico 5 (n + 1) → ∀ i : PreE7Sns2MenuIndex w,
        preE7Sns2MenuExceptional i (n - w) ≤
          K *
            (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
              (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
              (preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
            (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000) := by
  let epsilon : ℝ := 1 / 10000000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  obtain ⟨K, hK, hglobal⟩ := fusionCoarse_global_constant hcoarse hepsilon
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop 300] with n hn
  intro w hw i
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  let C := preE7Sns2MenuCertificate i
  let b := n - w
  let l := C.quotientRank
  let q := sns2RankTailTilt b l
  let M := b + 2 * q
  have hbn : b + w = n := Nat.sub_add_cancel hwn
  have hq : q ≤ n := sns2_tilt_le_ambient hwn l C.quotientRank_le
  have hM : M ≤ 3 * n := by dsimp [M]; omega
  have hMR : (M : ℝ) ≤ 3 * n := by exact_mod_cast hM
  have hM2 : (M : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (n : ℝ) - M)]
  have hs := hglobal M
  have hApos : 0 < preE7Sns2MenuNormalizer i :=
    preE7Sns2MenuNormalizer_pos i
  have hpoint0 := fusionWidthHot_pointing_denominator_le b w
  have hpoint : growingQuotientNormalizedPointing b w
      (preE7Sns2MenuNormalizer i) ≤
      (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
        (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 16 +
          5 * (n : ℝ) / 8 + 1 / 4)) /
        preE7Sns2MenuNormalizer i := by
    unfold growingQuotientNormalizedPointing
    calc
      _ = (((((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
          exactBenchmark (b + w)) / preE7Sns2MenuNormalizer i) := by ring
      _ ≤ (eulerProduct⁻¹ * ((((b + w + 1 : ℕ) : ℝ) ^ (b + w))) *
          (2 : ℝ) ^ (-(((b + w : ℕ) : ℝ) ^ 2) / 16 +
            5 * (((b + w : ℕ) : ℝ)) / 8 + 1 / 4)) /
          preE7Sns2MenuNormalizer i :=
        div_le_div_of_nonneg_right hpoint0 hApos.le
      _ = _ := by rw [hbn]
  have hmain :
      -((n : ℝ) ^ 2) / 16 - ((q : ℝ) - l) * (51 / 200) * b +
          (1 / 16 + epsilon) * (M : ℝ) ^ 2 + (l : ℝ) ^ 2 / 4 ≤
        -((n : ℝ) ^ 2) / 50000 := by
    by_cases hregime : l ≤ rankTail51Tilt b
    · have hsquare := C.square_completion b hregime
      have hgap := sns2_firstRegime_main_gap
        (b := b) (w := w) C.quotientRank_le
      have heps : epsilon * (M : ℝ) ^ 2 ≤
          9 * epsilon * (n : ℝ) ^ 2 := by
        calc
          _ ≤ epsilon * (9 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hM2 hepsilon.le
          _ = _ := by ring
      have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn
      have hqeq : q = rankTail51Tilt b := by
        dsimp [q, sns2RankTailTilt]
        exact max_eq_right hregime
      have hcertq : sns2RankTailTilt b C.quotientRank =
          rankTail51Tilt b := by
        unfold sns2RankTailTilt
        exact max_eq_right hregime
      rw [hcertq] at hsquare
      have hsquare' :
          (M : ℝ) ^ 2 / 16 - ((q : ℝ) - l) * (51 / 200) * b ≤
            (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 +
              (l : ℝ) * (51 / 200) * b + 1 / 4 := by
        dsimp [M]
        rw [hqeq]
        push_cast
        simpa only [l] using hsquare
      have hgap' :
          -((n : ℝ) ^ 2) / 16 + (b : ℝ) ^ 2 / 16 -
              (b : ℝ) ^ 2 / 40000 + (l : ℝ) * (51 / 200) * b +
              (l : ℝ) ^ 2 / 4 ≤ -((n : ℝ) ^ 2) / 40000 := by
        rw [hbn] at hgap
        simpa only [l] using hgap
      dsimp [epsilon] at heps ⊢
      nlinarith
    · have hregime' : rankTail51Tilt b < l := by omega
      have hsecond := C.second_regime b hregime'
      have hgap := sns2_secondRegime_quadratic_gap
        (b := b) (w := w) C.quotientRank_le hsecond.2
      have heps : epsilon * (M : ℝ) ^ 2 ≤
          9 * epsilon * (n : ℝ) ^ 2 := by
        calc
          _ ≤ epsilon * (9 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hM2 hepsilon.le
          _ = _ := by ring
      have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn
      have hqeq : q = l := by
        dsimp [q, l]
        exact hsecond.1
      have hgap' :
          -((n : ℝ) ^ 2) / 16 + (M : ℝ) ^ 2 / 16 +
              (l : ℝ) ^ 2 / 4 < -((n : ℝ) ^ 2) / 4944 := by
        rw [hbn] at hgap
        dsimp [M]
        rw [hqeq]
        push_cast
        simpa only [l] using hgap
      rw [hqeq]
      dsimp [epsilon] at heps ⊢
      nlinarith
  have hcoarseBound :
      (subgroupCount M : ℝ) ≤
        K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2) := hs
  unfold preE7Sns2MenuExceptional preE7Sns2ExceptionalScalar
  have hcoefficient :
      (preE7Sns2MenuCertificate i).normalCount *
          (preE7Sns2MenuCertificate i).outerFactor (n - w) =
        preE7Sns2MenuCoefficient i (n - w) := rfl
  have hnormalizer :
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i.1 : Set (Equiv.Perm (Fin w)))) : ℝ) =
        preE7Sns2MenuNormalizer i := rfl
  rw [hcoefficient, hnormalizer]
  rw [preE7Sns2MenuCoefficient_eq_normalized i (n - w)]
  dsimp only [C, b, l, q, M] at hcoarseBound hmain ⊢
  have hpoint_nonneg : 0 ≤ growingQuotientNormalizedPointing (n - w) w
      (preE7Sns2MenuNormalizer i) := by
    unfold growingQuotientNormalizedPointing
    have hfacpos : (0 : ℝ) < (n - w).factorial := by
      exact_mod_cast Nat.factorial_pos (n - w)
    exact div_nonneg
      (div_nonneg (div_nonneg (by positivity) hfacpos.le) hApos.le)
      (exactBenchmark_pos (n - w + w)).le
  have htail :
      (2 : ℝ) ^
            (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
          (subgroupCount
            (n - w + 2 * sns2RankTailTilt (n - w) C.quotientRank) : ℝ) ≤
        (2 : ℝ) ^
            (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
          (K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
    simpa only [C, M, q, l, b] using
      (mul_le_mul_of_nonneg_left hcoarseBound (by positivity))
  have hsource :
      (preE7Sns2NormalizedCoefficient i (n - w) *
          (2 : ℝ) ^ ((C.quotientRank : ℝ) ^ 2 / 4)) *
        ((2 : ℝ) ^
            (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
          (subgroupCount
            (n - w + 2 * sns2RankTailTilt (n - w) C.quotientRank) : ℝ)) ≤
      (preE7Sns2NormalizedCoefficient i (n - w) *
          (2 : ℝ) ^ ((C.quotientRank : ℝ) ^ 2 / 4)) *
        ((2 : ℝ) ^
            (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
          (K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) :=
    mul_le_mul_of_nonneg_left htail
      (mul_nonneg (preE7Sns2NormalizedCoefficient_nonneg i (n - w))
        (by positivity))
  calc
    _ ≤ growingQuotientNormalizedPointing (n - w) w
          (preE7Sns2MenuNormalizer i) *
        (preE7Sns2NormalizedCoefficient i (n - w) *
            (2 : ℝ) ^ ((C.quotientRank : ℝ) ^ 2 / 4) *
          ((2 : ℝ) ^
              (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                  C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
            (K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)))) := by
      exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hsource)
        hpoint_nonneg
    _ ≤ ((eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 16 +
            5 * (n : ℝ) / 8 + 1 / 4)) /
          preE7Sns2MenuNormalizer i) *
        (preE7Sns2NormalizedCoefficient i (n - w) *
            (2 : ℝ) ^ ((C.quotientRank : ℝ) ^ 2 / 4) *
          ((2 : ℝ) ^
              (-(((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                  C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ))) *
            (K * (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)))) := by
      exact mul_le_mul_of_nonneg_right hpoint
        (mul_nonneg
          (mul_nonneg (preE7Sns2NormalizedCoefficient_nonneg i (n - w))
            (by positivity))
          (mul_nonneg (by positivity)
            (mul_nonneg hK.le (by positivity))))
    _ = K *
          (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
            (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
            (preE7Sns2NormalizedCoefficient i (n - w) /
              preE7Sns2MenuNormalizer i)) *
          (2 : ℝ) ^
            (-((n : ℝ) ^ 2) / 16 -
              ((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ) +
              (1 / 16 + epsilon) * (M : ℝ) ^ 2 +
              (C.quotientRank : ℝ) ^ 2 / 4) := by
      rw [div_eq_mul_inv]
      rw [show -((n : ℝ) ^ 2) / 16 + 5 * (n : ℝ) / 8 + 1 / 4 =
          (5 * (n : ℝ) / 8 + 1 / 4) + (-((n : ℝ) ^ 2) / 16) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -((n : ℝ) ^ 2) / 16 -
              ((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ) +
              (1 / 16 + epsilon) * (M : ℝ) ^ 2 +
              (C.quotientRank : ℝ) ^ 2 / 4 =
          (-((n : ℝ) ^ 2) / 16) +
            (-((sns2RankTailTilt (n - w) C.quotientRank : ℝ) -
                C.quotientRank) * (51 / 200) * ((n - w : ℕ) : ℝ)) +
            ((1 / 16 + epsilon) * (M : ℝ) ^ 2) +
            ((C.quotientRank : ℝ) ^ 2 / 4) by ring]
      repeat' rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ K *
          (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
            (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
            (preE7Sns2NormalizedCoefficient i (n - w) /
              preE7Sns2MenuNormalizer i)) *
          (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000) := by
      have hP0 : 0 ≤
          eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
            (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
            (preE7Sns2NormalizedCoefficient i (n - w) /
              preE7Sns2MenuNormalizer i) :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity))
            (by positivity))
          (div_nonneg (preE7Sns2NormalizedCoefficient_nonneg i (n - w))
            hApos.le)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hmain)
        (mul_nonneg hK.le hP0)
    _ = _ := rfl

/-- The complete literal SNS2 hot menu has quadratic decay. -/
noncomputable def preE7Sns2Hot_exponentialScalarBound
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hmass : PreE7Sns2NormalizedMenuMassBound) :
    ExponentialScalarBound
      (growingQuotientExceptionalTotal 5
        (fun w i => preE7Sns2MenuExceptional (w := w) i)) := by
  let hexists := sns2_hot_entry_le hcoarse
  let K : ℝ := Classical.choose hexists
  have hK : 0 < K := (Classical.choose_spec hexists).1
  have hentry := (Classical.choose_spec hexists).2
  have hoverhead := growingMenuMass_hot_overhead
    (ρ := (1 / 100 : ℝ)) 5
    (fun w i => preE7Sns2NormalizedCoefficient (w := w) i)
    (fun w i => preE7Sns2MenuNormalizer (w := w) i)
    (by norm_num)
    (fun w i b => preE7Sns2NormalizedCoefficient_nonneg i b)
    (fun w i => preE7Sns2MenuNormalizer_pos i) hmass
  let hentryWitness := eventually_atTop.mp hentry
  let Nentry : ℕ := Classical.choose hentryWitness
  have hNentry := Classical.choose_spec hentryWitness
  let hoverWitness := eventually_atTop.mp hoverhead
  let Nover : ℕ := Classical.choose hoverWitness
  have hNover := Classical.choose_spec hoverWitness
  refine
    { threshold := max (max Nentry Nover) 1
      rate := 1 / 80000
      constant := K
      rate_pos := by norm_num
      constant_pos := hK
      bound := ?_ }
  intro n hn
  have hninner : max Nentry Nover ≤ n := (le_max_left _ _).trans hn
  have hnentry : Nentry ≤ n := (le_max_left _ _).trans hninner
  have hnover : Nover ≤ n := (le_max_right _ _).trans hninner
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hsum : growingQuotientExceptionalTotal 5
      (fun w i => preE7Sns2MenuExceptional (w := w) i) n ≤
      K *
        (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico 5 (n + 1),
            ∑ i : PreE7Sns2MenuIndex w,
              preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
        (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000) := by
    unfold growingQuotientExceptionalTotal
    calc
      _ ≤ ∑ w ∈ Finset.Ico 5 (n + 1), ∑ i : PreE7Sns2MenuIndex w,
          K *
            (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
              (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
              (preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
            (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000) := by
        exact Finset.sum_le_sum fun w hw =>
          Finset.sum_le_sum fun i _ => hNentry n hnentry w hw i
      _ = _ := by
        let P : ℝ := eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4)
        let R : ℝ := (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000)
        change (∑ w ∈ Finset.Ico 5 (n + 1),
            ∑ i : PreE7Sns2MenuIndex w,
              K * (P * (preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) * R) =
          K * (P * (∑ w ∈ Finset.Ico 5 (n + 1),
            ∑ i : PreE7Sns2MenuIndex w,
              preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) * R
        calc
          _ = ∑ w ∈ Finset.Ico 5 (n + 1),
              K * (P * (∑ i : PreE7Sns2MenuIndex w,
                preE7Sns2NormalizedCoefficient i (n - w) /
                  preE7Sns2MenuNormalizer i)) * R := by
            apply Finset.sum_congr rfl
            intro w _
            symm
            calc
              _ = (K * P * (∑ i : PreE7Sns2MenuIndex w,
                    preE7Sns2NormalizedCoefficient i (n - w) /
                      preE7Sns2MenuNormalizer i)) * R := by ring
              _ = (∑ i : PreE7Sns2MenuIndex w,
                    K * P * (preE7Sns2NormalizedCoefficient i (n - w) /
                      preE7Sns2MenuNormalizer i)) * R := by
                    rw [Finset.mul_sum]
              _ = _ := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = _ := by
            symm
            calc
              _ = (K * P * (∑ w ∈ Finset.Ico 5 (n + 1),
                    ∑ i : PreE7Sns2MenuIndex w,
                      preE7Sns2NormalizedCoefficient i (n - w) /
                        preE7Sns2MenuNormalizer i)) * R := by ring
              _ = (∑ w ∈ Finset.Ico 5 (n + 1),
                    K * P * (∑ i : PreE7Sns2MenuIndex w,
                      preE7Sns2NormalizedCoefficient i (n - w) /
                        preE7Sns2MenuNormalizer i)) * R := by
                    rw [Finset.mul_sum]
              _ = _ := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro w _
                ring
  have hover := hNover n hnover
  have hquad :
      (1 / 100 : ℝ) ^ 2 * (n : ℝ) ^ 2 / 16 -
          (n : ℝ) ^ 2 / 50000 ≤
        -(1 / 80000 : ℝ) * (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
      (sub_nonneg.mpr hnR)]
  calc
    _ ≤ K *
        (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico 5 (n + 1),
            ∑ i : PreE7Sns2MenuIndex w,
              preE7Sns2NormalizedCoefficient i (n - w) /
                preE7Sns2MenuNormalizer i)) *
        (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000) := hsum
    _ ≤ K * (2 : ℝ) ^
        (((1 / 100 : ℝ) ^ 2 * (n : ℝ) ^ 2 / 16) -
          (n : ℝ) ^ 2 / 50000) := by
      calc
        _ ≤ K * ((2 : ℝ) ^
              ((1 / 100 : ℝ) ^ 2 * (n : ℝ) ^ 2 / 16) *
            (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 50000)) :=
          by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hover (by positivity)) hK.le
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          ring
    _ ≤ K * (2 : ℝ) ^ (-(1 / 80000 : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hquad) hK.le

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
