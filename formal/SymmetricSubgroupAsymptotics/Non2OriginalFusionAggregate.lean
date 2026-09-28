import SymmetricSubgroupAsymptotics.Non2OriginalFusion
import SymmetricSubgroupAsymptotics.FusionDirectAggregate

/-!
# Varying-width aggregate for retained nonbinary fusion

The retained cut has shifted half-width at most `21/32` of its original
half-width and fusion gap at least `s/768`.  These constants give a uniform
pointwise direct-kernel estimate.  After an explicit original-weight menu
mass bound, the sum over every width is exponentially small.  The mass bound
remains a visible physical obligation; this file performs the complete
numerical aggregation once it is supplied.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniform direct-kernel estimate at the exact constants supplied by the
retained nonbinary cut. -/
theorem fusionDirectKernel_le_non2 (b h r : ℕ)
    (hprefix : 32 * r ≤ 21 * h)
    {D a e : ℝ} (hD : 0 ≤ D) (ha : 0 < a)
    (hgap : (h : ℝ) / 768 ≤ e) :
    fusionDirectKernel b h (2 * r) D a e ≤
      (eulerProduct⁻¹ ^ 2 * (D / a)) *
        ((b + 2 * h + 1 : ℕ) : ℝ) ^ (h + r + 1) *
          (2 : ℝ) ^ (-((h : ℝ) * (b : ℝ)) / 384 -
            583 * (h : ℝ) ^ 2 / 4096 + (h : ℝ) / 4 + 1 / 4) := by
  have hr : r ≤ h := by omega
  have hp : 32 * (r : ℝ) ≤ 21 * (h : ℝ) := by
    exact_mod_cast hprefix
  have hsquare : 1024 * (r : ℝ) ^ 2 ≤ 441 * (h : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp)
      (show 0 ≤ 21 * (h : ℝ) + 32 * (r : ℝ) by positivity)]
  have hg : (h : ℝ) ≤ 768 * e := by linarith
  have hlinear : -2 * e * (b : ℝ) ≤
      -(h : ℝ) * (b : ℝ) / 384 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg)
      (Nat.cast_nonneg (α := ℝ) b)]
  apply (fusionDirectKernel_le_uniform b h r hr hD ha).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

namespace Non2OriginalFusionCertificate

variable {B : Type} [Group B]
variable {M : Rep (ZMod 2) B} {s : ℕ}

/-- Pointwise numerical envelope in the certificate's native parameters. -/
theorem directKernel_le
    (C : Non2OriginalFusionCertificate M s) (heven : Even s)
    (b : ℕ) {a : ℝ} (ha : 0 < a) :
    fusionDirectKernel b s C.prefixDegree C.liftConstant a C.gapParameter ≤
      (eulerProduct⁻¹ ^ 2 * (C.liftConstant / a)) *
        ((b + 2 * s + 1 : ℕ) : ℝ) ^ (s + C.markerHalf + 1) *
          (2 : ℝ) ^ (-((s : ℝ) * (b : ℝ)) / 384 -
            583 * (s : ℝ) ^ 2 / 4096 + (s : ℝ) / 4 + 1 / 4) := by
  rw [C.prefixDegree_eq_two_mul_markerHalf heven]
  exact fusionDirectKernel_le_non2 b s C.markerHalf C.markerHalf_strong
    C.liftConstant_nonneg ha C.gap_ge

end Non2OriginalFusionCertificate

/-- The polynomial base is eventually absorbed at rate `1/512`. -/
theorem fusionNon2_polynomial_base_eventually :
    ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) / 512) := by
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 3
    (show (0 : ℝ) < 1 / 512 by norm_num), eventually_ge_atTop 4096]
      with n hn hlarge
  have hnr : (4096 : ℝ) ≤ n := by exact_mod_cast hlarge
  have hbound : (((n + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ)) *
      (2 : ℝ) ^ (-(n : ℝ) / 512) ≤
        (2 : ℝ) ^ (7 / 2 - (n : ℝ) / 1024) := by
    calc
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) *
          (((n + 1 : ℕ) : ℝ) ^ 3 *
            (2 : ℝ) ^ (-(1 / 512 : ℝ) * (n : ℝ))) := by
        have he : -(n : ℝ) / 512 = -(1 / 512 : ℝ) * (n : ℝ) := by ring
        rw [he]
        ring
      _ ≤ (2 : ℝ) ^ (1 / 2 : ℝ) *
          (((1 + 1 : ℕ) : ℝ) ^ 3 *
            (2 : ℝ) ^ (-((1 / 512 : ℝ) / 2) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
        have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [← mul_assoc, h8,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
  have hone : (2 : ℝ) ^ (7 / 2 - (n : ℝ) / 1024) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2)
      (show 7 / 2 - (n : ℝ) / 1024 ≤ 0 by linarith)
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos
    (by norm_num : (0 : ℝ) < 2) (-(n : ℝ) / 512))).mp
  calc
    (2 : ℝ) ^ (-(n : ℝ) / 512) *
        (((n + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ)) =
      (((n + 1 : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ)) *
        (2 : ℝ) ^ (-(n : ℝ) / 512) := mul_comm _ _
    _ ≤ 1 := hbound.trans hone
    _ = (2 : ℝ) ^ (-(n : ℝ) / 512) *
        (2 : ℝ) ^ ((n : ℝ) / 512) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -(n : ℝ) / 512 + (n : ℝ) / 512 = 0 by ring,
        Real.rpow_zero]

/-- One varying entry menu at a fixed half-width.  The physical hypothesis
is exactly the original-weight mass `Σ D/a`; entry count alone is not used. -/
theorem fusionNon2Direct_width_sum_le {ι : Type*} [Fintype ι]
    (b h : ℕ) (hh : 1 ≤ h) (r : ι → ℕ) (D a e : ι → ℝ) (H : ℝ)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i)
    (hprefix : ∀ i, 32 * r i ≤ 21 * h)
    (hgap : ∀ i, (h : ℝ) / 768 ≤ e i)
    (hmass : (∑ i, D i / a i) ≤
      (2 : ℝ) ^ ((h : ℝ) ^ 2 / 32 + H))
    (hpoly : ((b + 2 * h + 1 : ℕ) : ℝ) ^ 3 *
      (2 : ℝ) ^ (1 / 2 : ℝ) ≤
        (2 : ℝ) ^ (((b + 2 * h : ℕ) : ℝ) / 512)) :
    (∑ i, fusionDirectKernel b h (2 * r i) (D i) (a i) (e i)) ≤
      (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H) *
        (2 : ℝ) ^ (-(h : ℝ) * ((b + 2 * h : ℕ) : ℝ) / 2048) := by
  let X : ℝ := ((b + 2 * h + 1 : ℕ) : ℝ)
  let E : ℝ := -((h : ℝ) * (b : ℝ)) / 384 -
    583 * (h : ℝ) ^ 2 / 4096 + (h : ℝ) / 4 + 1 / 4
  have hX : 1 ≤ X := by
    dsimp [X]
    exact_mod_cast (show 1 ≤ b + 2 * h + 1 by omega)
  have hentry (i : ι) :
      fusionDirectKernel b h (2 * r i) (D i) (a i) (e i) ≤
        (D i / a i) *
          (eulerProduct⁻¹ ^ 2 * X ^ (3 * h) * (2 : ℝ) ^ E) := by
    have hr : h + r i + 1 ≤ 3 * h := by
      have := hprefix i
      omega
    calc
      _ ≤ (eulerProduct⁻¹ ^ 2 * (D i / a i)) *
          X ^ (h + r i + 1) * (2 : ℝ) ^ E :=
        by simpa only [X, E] using
          fusionDirectKernel_le_non2 b h (r i) (hprefix i)
            (hD i) (ha i) (hgap i)
      _ ≤ (eulerProduct⁻¹ ^ 2 * (D i / a i)) *
          X ^ (3 * h) * (2 : ℝ) ^ E := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcoef : 0 ≤ eulerProduct⁻¹ ^ 2 * (D i / a i) :=
          mul_nonneg (sq_nonneg _) (div_nonneg (hD i) (ha i).le)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hr) hcoef
      _ = _ := by ring
  have hmassBound :
      (∑ i, fusionDirectKernel b h (2 * r i) (D i) (a i) (e i)) ≤
        (2 : ℝ) ^ ((h : ℝ) ^ 2 / 32 + H) *
          (eulerProduct⁻¹ ^ 2 * X ^ (3 * h) * (2 : ℝ) ^ E) := by
    calc
      _ ≤ ∑ i, (D i / a i) *
          (eulerProduct⁻¹ ^ 2 * X ^ (3 * h) * (2 : ℝ) ^ E) :=
        Finset.sum_le_sum (fun i _ => hentry i)
      _ = (∑ i, D i / a i) *
          (eulerProduct⁻¹ ^ 2 * X ^ (3 * h) * (2 : ℝ) ^ E) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)
  calc
    _ ≤ (2 : ℝ) ^ ((h : ℝ) ^ 2 / 32 + H) *
        (eulerProduct⁻¹ ^ 2 * X ^ (3 * h) * (2 : ℝ) ^ E) := hmassBound
    _ = (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H) * X ^ (3 * h) *
        (2 : ℝ) ^ ((h : ℝ) ^ 2 / 32 + E) := by
      simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H) * X ^ (3 * h) *
        (2 : ℝ) ^ (-(h : ℝ) * (b : ℝ) / 384 -
          455 * (h : ℝ) ^ 2 / 4096 + (h : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [E]
      have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
      linarith
    _ = (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H) *
        (X ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ)) ^ h *
          (2 : ℝ) ^ (-(h : ℝ) * (b : ℝ) / 384 -
            455 * (h : ℝ) ^ 2 / 4096) := by
      rw [mul_pow, ← pow_mul,
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H) *
        ((2 : ℝ) ^ (((b + 2 * h : ℕ) : ℝ) / 512)) ^ h *
          (2 : ℝ) ^ (-(h : ℝ) * (b : ℝ) / 384 -
            455 * (h : ℝ) ^ 2 / 4096) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpoly h) (by positivity)
    _ ≤ _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) b,
        sq_nonneg (h : ℝ)]

/-- The numerical sum over every retained half-width.  Widths below `24`
are deliberately absent and may be handled by a fixed finite menu. -/
def fusionNon2WideDirectSum {ι : ℕ → Type*} [∀ h, Fintype (ι h)]
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (n : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (n + 1), if 24 ≤ h ∧ 2 * h ≤ n then
    ∑ i, fusionDirectKernel (n - 2 * h) h (2 * r h i)
      (D h i) (a h i) (e h i) else 0

/-- A uniform original-weight menu-mass bound gives exponential aggregate
decay across all widths.  This theorem does not manufacture that physical
mass bound or a subgroup-family cover. -/
theorem fusionNon2WideDirectSum_eventually
    {ι : ℕ → Type*} [∀ h, Fintype (ι h)]
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (H : ℝ)
    (hD : ∀ h i, 0 ≤ D h i) (ha : ∀ h i, 0 < a h i)
    (hprefix : ∀ h i, 32 * r h i ≤ 21 * h)
    (hgap : ∀ (h : ℕ) i, (h : ℝ) / 768 ≤ e h i)
    (hmass : ∀ h, 24 ≤ h →
      (∑ i, D h i / a h i) ≤ (2 : ℝ) ^ ((h : ℝ) ^ 2 / 32 + H)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      fusionNon2WideDirectSum r D a e n ≤
        C * (2 : ℝ) ^ (-3 * (n : ℝ) / 512) := by
  let A : ℝ := eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ H
  have hA : 0 < A := by
    dsimp [A]
    have := euler_positive
    positivity
  refine ⟨2 * A, by positivity, ?_⟩
  filter_upwards [fusionNon2_polynomial_base_eventually,
    eventually_shifted_natpow_mul_exponential_le 1 1
      (show (0 : ℝ) < 3 / 256 by norm_num)] with n hpoly hdecay
  have hentry (h : ℕ) :
      (if 24 ≤ h ∧ 2 * h ≤ n then
        ∑ i, fusionDirectKernel (n - 2 * h) h (2 * r h i)
          (D h i) (a h i) (e h i) else 0) ≤
        A * (2 : ℝ) ^ (-3 * (n : ℝ) / 256) := by
    split_ifs with hh
    · have hn : n - 2 * h + 2 * h = n := Nat.sub_add_cancel hh.2
      have hb := fusionNon2Direct_width_sum_le (n - 2 * h) h
        (by omega) (r h) (D h) (a h) (e h) H
        (hD h) (ha h) (hprefix h) (hgap h) (hmass h hh.1)
        (by simpa only [hn] using hpoly)
      rw [hn] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hhr : (24 : ℝ) ≤ h := by exact_mod_cast hh.1
      nlinarith [mul_nonneg (sub_nonneg.mpr hhr)
        (Nat.cast_nonneg (α := ℝ) n)]
    · positivity
  have hsum : fusionNon2WideDirectSum r D a e n ≤
      A * (((n + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-3 * (n : ℝ) / 256)) := by
    unfold fusionNon2WideDirectSum
    apply (Finset.sum_le_sum (fun h _ => hentry h)).trans_eq
    simp
    ring
  apply hsum.trans
  have hd : ((n + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-3 * (n : ℝ) / 256) ≤
        2 * (2 : ℝ) ^ (-3 * (n : ℝ) / 512) := by
    have he1 : -(3 / 256 : ℝ) * (n : ℝ) =
        -3 * (n : ℝ) / 256 := by ring
    have he2 : -((3 / 256 : ℝ) / 2) * (n : ℝ) =
        -3 * (n : ℝ) / 512 := by ring
    simpa only [pow_one, Nat.reduceAdd, Nat.cast_ofNat, he1, he2] using hdecay
  calc
    _ ≤ A * (2 * (2 : ℝ) ^ (-3 * (n : ℝ) / 512)) :=
      mul_le_mul_of_nonneg_left hd hA.le
    _ = _ := by ring

end SymmetricSubgroupAsymptotics

end
