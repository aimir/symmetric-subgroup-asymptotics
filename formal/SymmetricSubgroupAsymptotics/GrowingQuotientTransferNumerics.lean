import SymmetricSubgroupAsymptotics.CompleteQuotientMoment
import SymmetricSubgroupAsymptotics.FusionNumerics

/-!
# Numerical core of growing-parameter quotient transfer

The complete quotient moment is first exposed as a nonnegative real-valued
fusion weight.  Its hot tail is then controlled at every positive threshold.
The remaining lemmas isolate the rounded moment choice and the uniform
quadratic exponent calculation used when the quotient representation degree
is allowed to grow with the removed orbit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {R : Type*} [Group R] [Finite R]

/-- Real-valued form of the complete literal quotient-map count. -/
def completeQuotientWeight {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  completeQuotientCount (R := R) J

theorem completeQuotientWeight_nonneg {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    0 ≤ completeQuotientWeight (R := R) J := by
  unfold completeQuotientWeight
  exact Nat.cast_nonneg _

/-- The exact complete quotient moment in the real-valued interface used by
the hot/cold fusion inequalities. -/
theorem completeQuotientWeight_moment_le {s : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := R) J ^ q) ≤
      (subgroupCount (b + q * s) : ℝ) := by
  unfold completeQuotientWeight
  exact_mod_cast completeQuotientCount_moment_le ρ hρ b q

/-- Markov's inequality in the exact form needed here.  The moment bound is
the proved simultaneous quotient-graph injection, so literal normal axes and
coincident quotient maps remain present in every power. -/
theorem completeQuotientWeight_hot_sum_le {s : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (b q : ℕ) (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) :
    (∑ J ∈ Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) ↦
          t < completeQuotientWeight (R := R) J),
        completeQuotientWeight (R := R) J) ≤
      1 / t ^ (q - 1) * (subgroupCount (b + q * s) : ℝ) := by
  simpa only [one_mul] using
    (fusion_hot_sum_le
      (fun J : Subgroup (Equiv.Perm (Fin b)) ↦
        completeQuotientWeight (R := R) J)
      (fun J : Subgroup (Equiv.Perm (Fin b)) ↦
        completeQuotientWeight (R := R) J)
      (D := 1) (t := t) (M := (subgroupCount (b + q * s) : ℝ))
      (by norm_num) ht (completeQuotientWeight_nonneg (R := R))
      (by intro J; simp)
      hq (completeQuotientWeight_moment_le ρ hρ b q))

/-- The positive integer moment used by the growing-parameter transfer. -/
def growingQuotientMoment (δ v b : ℝ) : ℕ :=
  fusionMoment (δ / 2) v b

theorem growingQuotientMoment_pos (δ v b : ℝ) :
    1 ≤ growingQuotientMoment δ v b :=
  fusionMoment_pos (δ / 2) v b

/-- Rounding the optimizing real moment costs at most one. -/
theorem growingQuotientMoment_distance {δ v b : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    0 ≤ (growingQuotientMoment δ v b : ℝ) - 4 * δ * b / v ^ 2 ∧
      (growingQuotientMoment δ v b : ℝ) - 4 * δ * b / v ^ 2 ≤ 1 := by
  have h := fusionMoment_distance (e := δ / 2) (v := v) (b := b)
    (by linarith) hb
  change 0 ≤ (fusionMoment (δ / 2) v b : ℝ) - 4 * δ * b / v ^ 2 ∧
    (fusionMoment (δ / 2) v b : ℝ) - 4 * δ * b / v ^ 2 ≤ 1
  rw [show 4 * δ * b / v ^ 2 = 8 * (δ / 2) * b / v ^ 2 by ring]
  exact h

/-- Exact completion of the square for the parametric hot exponent. -/
theorem growingQuotient_hot_square (b w v δ η a q : ℝ)
    (hv : v ≠ 0) (ha : a = v / 8 + δ / 2) :
    (b + q * v) ^ 2 / 16 - (q - 1) * a * b + η * b -
        (b + w) ^ 2 / 16 =
      -δ ^ 2 * b ^ 2 / v ^ 2 + (η + a - w / 8) * b - w ^ 2 / 16 +
        v ^ 2 / 16 * (q - 4 * δ * b / v ^ 2) ^ 2 := by
  rw [ha]
  field_simp
  ring

/-- The rounded moment retains the full uniform quadratic reserve.  The
assumption on `η+a-w/8` is exactly the parity-safe margin after replacing the
even part of the removed width by the physical width. -/
theorem growingQuotient_hot_exponent_le
    {ρ δ v b w η a : ℝ}
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hw : 0 ≤ w) (hv : 0 < v)
    (hratio : ρ / 2 ≤ δ / v)
    (hvupper : v ≤ (1 - 4 * ρ) * w)
    (hδlower : ρ * w / 2 ≤ δ)
    (hmargin : η + a - w / 8 ≤ -δ / 2)
    (ha : a = v / 8 + δ / 2) :
    (b + (growingQuotientMoment δ v b : ℝ) * v) ^ 2 / 16 -
        ((growingQuotientMoment δ v b : ℝ) - 1) * a * b + η * b -
          (b + w) ^ 2 / 16 ≤
      -(ρ ^ 2) * (b + w) ^ 2 / 4 := by
  let q : ℝ := growingQuotientMoment δ v b
  obtain ⟨hqlo, hqhi⟩ := growingQuotientMoment_distance hδ hb (v := v)
  have hqsq : (q - 4 * δ * b / v ^ 2) ^ 2 ≤ 1 := by
    dsimp [q]
    nlinarith
  have hρ0 : 0 ≤ ρ := hρ.le
  have hv0 : 0 ≤ v := hv.le
  have hcap0 : 0 ≤ 1 - 4 * ρ := by nlinarith
  have hwcap0 : 0 ≤ (1 - 4 * ρ) * w := mul_nonneg hcap0 hw
  have hratio0 : 0 ≤ ρ / 2 := by positivity
  have hδv0 : 0 ≤ δ / v := hratio0.trans hratio
  have hratioSq : (ρ / 2) ^ 2 ≤ (δ / v) ^ 2 :=
    (sq_le_sq₀ hratio0 hδv0).2 hratio
  have hδdiv : δ ^ 2 / v ^ 2 = (δ / v) ^ 2 := by
    field_simp
  have hvSq : v ^ 2 ≤ ((1 - 4 * ρ) * w) ^ 2 :=
    (sq_le_sq₀ hv0 hwcap0).2 hvupper
  have hround : v ^ 2 / 16 *
      (q - 4 * δ * b / v ^ 2) ^ 2 ≤
      ((1 - 4 * ρ) * w) ^ 2 / 16 := by
    calc
      _ ≤ v ^ 2 / 16 * 1 :=
        mul_le_mul_of_nonneg_left hqsq (by positivity)
      _ ≤ ((1 - 4 * ρ) * w) ^ 2 / 16 := by nlinarith
  have hratioTerm :
      -δ ^ 2 * b ^ 2 / v ^ 2 ≤ -(ρ ^ 2) * b ^ 2 / 4 := by
    rw [show -δ ^ 2 * b ^ 2 / v ^ 2 = -(δ ^ 2 / v ^ 2) * b ^ 2 by ring,
      hδdiv]
    have hbSq : 0 ≤ b ^ 2 := sq_nonneg b
    nlinarith [mul_nonneg (sub_nonneg.mpr hratioSq) hbSq]
  have hlinear : (η + a - w / 8) * b ≤ -ρ * w * b / 4 := by
    have hm := mul_le_mul_of_nonneg_right hmargin hb
    have hd := mul_le_mul_of_nonneg_right hδlower hb
    nlinarith
  have hmain :
      -δ ^ 2 * b ^ 2 / v ^ 2 + (η + a - w / 8) * b - w ^ 2 / 16 +
          v ^ 2 / 16 * (q - 4 * δ * b / v ^ 2) ^ 2 ≤
        -(ρ ^ 2) * b ^ 2 / 4 - ρ * w * b / 4 -
          (ρ / 2 - ρ ^ 2) * w ^ 2 := by
    calc
      _ ≤ -(ρ ^ 2) * b ^ 2 / 4 - ρ * w * b / 4 - w ^ 2 / 16 +
          ((1 - 4 * ρ) * w) ^ 2 / 16 := by linarith
      _ = _ := by ring
  have hfinal :
      -(ρ ^ 2) * b ^ 2 / 4 - ρ * w * b / 4 -
          (ρ / 2 - ρ ^ 2) * w ^ 2 ≤
        -(ρ ^ 2) * (b + w) ^ 2 / 4 := by
    have h₁ : 0 ≤ 1 - 2 * ρ := by nlinarith
    have h₂ : 0 ≤ 2 - 5 * ρ := by nlinarith
    have hfactor : 0 ≤ ρ * w / 4 *
        (b * (1 - 2 * ρ) + w * (2 - 5 * ρ)) := by positivity
    calc
      _ = -(ρ ^ 2) * (b + w) ^ 2 / 4 - ρ * w / 4 *
          (b * (1 - 2 * ρ) + w * (2 - 5 * ρ)) := by ring
      _ ≤ -(ρ ^ 2) * (b + w) ^ 2 / 4 := sub_le_self _ hfactor
  rw [growingQuotient_hot_square b w v δ η a q hv.ne' ha]
  exact hmain.trans hfinal

end SymmetricSubgroupAsymptotics

end
