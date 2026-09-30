import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogue

/-!
# Quadratic decay of the B6 rank-tail scalar

The exact square completion in the B6 certificate cancels the coarse
`b^2/16` term.  The remaining `-b^2/10000` deficit absorbs the elementary
factorial fibre bound.  This file carries that calculation through the exact
benchmark pointing, leaving a uniform quadratic exponential decay for every
certified B6 action.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A successor grows more slowly than every fixed positive exponential.
This public form is also useful for the other source-summed rank-tail
families. -/
theorem eventually_succ_le_two_rpow {gamma : ℝ} (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (gamma * n) := by
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 1 hgamma,
    eventually_exponential_le_inv_rpow
      (show 0 < gamma / 2 by positivity) 1,
    eventually_ge_atTop 2] with n hpoly hexp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-(gamma / 2) * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hsmall : ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-gamma * n) ≤ 1 := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ (-(gamma / 2) * n) := by simpa using hpoly
      _ ≤ 2 * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp' (by norm_num)
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_iff₀ hnpos).2 (by
          simpa using (show (2 : ℝ) ≤ n by exact_mod_cast hn))
  calc
    ((n + 1 : ℕ) : ℝ) =
        (((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-gamma * n)) *
          (2 : ℝ) ^ (gamma * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -gamma * (n : ℝ) + gamma * n = 0 by ring,
        Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (gamma * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

private theorem b6_rankTail_degree_le_three_mul (b : ℕ) (hb : 1 ≤ b) :
    b + 2 * b6RankTailExponent b ≤ 3 * b := by
  unfold b6RankTailExponent
  omega

/-- The exceptional B6 term has a fixed quadratic deficit.  Certificate
constants remain outside the exponential and the original normalizer is
retained throughout the comparison. -/
theorem preE7B6ExceptionalScalar_eventually
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) :
    ∀ᶠ b : ℕ in atTop,
      preE7B6ExceptionalScalar C b ≤
        (eulerProduct⁻¹ * C.normalCount) *
          (2 : ℝ) ^ (-((b : ℝ) ^ 2) / 20000) := by
  have hw := C.width_eq
  subst w
  let epsilon : ℝ := 1 / 1000000
  let gamma : ℝ := 1 / 1000000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by norm_num [gamma]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoarse epsilon hepsilon)
  filter_upwards [eventually_ge_atTop (max N 12),
    eventually_succ_le_two_rpow hgamma] with b hb hsucc
  let q : ℕ := b6RankTailExponent b
  let M : ℕ := b + 2 * q
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hb12 : 12 ≤ b := (le_max_right _ _).trans hb
  have hb1 : 1 ≤ b := by omega
  have hbM : b ≤ M := Nat.le_add_right _ _
  have hMN : N ≤ M := hbN.trans hbM
  have hM3 : M ≤ 3 * b := by
    simpa only [M, q] using b6_rankTail_degree_le_three_mul b hb1
  have hM3R : (M : ℝ) ≤ 3 * (b : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ 9 * (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (b : ℝ) - M)]
  have hs := hN M hMN
  have hpoint0 := fusionHot_pointing_denominator_le b 6 (by omega)
  have hA : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
      (preE7NonPairAction 12 i : Set (Equiv.Perm (Fin 12)))) := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (preE7NonPairAction 12 i : Set (Equiv.Perm (Fin 12)))))
  have hpoint : growingQuotientNormalizedPointing b 12
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction 12 i : Set (Equiv.Perm (Fin 12)))) : ℝ) ≤
      eulerProduct⁻¹ *
        (2 : ℝ) ^ (-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4) := by
    unfold growingQuotientNormalizedPointing
    calc
      _ ≤ (((b + 12).factorial : ℝ) / (b.factorial : ℝ)) /
          exactBenchmark (b + 12) := by
        have hnum : 0 ≤ (((b + 12).factorial : ℝ) /
            (b.factorial : ℝ)) := by positivity
        have hbench : 0 < exactBenchmark (b + 12) :=
          exactBenchmark_pos (b + 12)
        apply div_le_div_of_nonneg_right _ hbench.le
        exact div_le_self hnum hA
      _ ≤ _ := hpoint0
  have hfacNat := factorial_le_succ_pow b
  have hfac : ((b.factorial : ℕ) : ℝ) ^ 16 ≤
      (2 : ℝ) ^ (16 * gamma * (b : ℝ) ^ 2) := by
    have hfacR : ((b.factorial : ℕ) : ℝ) ≤
        (((b + 1 : ℕ) : ℝ) ^ b) := by exact_mod_cast hfacNat
    have hpow := pow_le_pow_left₀ (by positivity) hfacR 16
    have hsuccpow := pow_le_pow_left₀ (by positivity) hsucc (16 * b)
    calc
      ((b.factorial : ℕ) : ℝ) ^ 16 ≤
          ((((b + 1 : ℕ) : ℝ) ^ b) ^ 16) := hpow
      _ = (((b + 1 : ℕ) : ℝ) ^ (16 * b)) := by ring
      _ ≤ (((2 : ℝ) ^ (gamma * b)) ^ (16 * b)) := hsuccpow
      _ = (2 : ℝ) ^ (16 * gamma * (b : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring
  have hsquare := C.square_completion b
  have hexponent :
      (-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4) +
        16 * gamma * (b : ℝ) ^ 2 +
        (-((q : ℝ) * (13 / 50) * b)) +
        (1 / 16 + epsilon) * (M : ℝ) ^ 2 ≤
          -((b : ℝ) ^ 2) / 20000 := by
    have heM : epsilon * (M : ℝ) ^ 2 ≤
        9 * epsilon * (b : ℝ) ^ 2 := by
      calc
        _ ≤ epsilon * (9 * (b : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hM2 hepsilon.le
        _ = _ := by ring
    have hsquare' :
        (M : ℝ) ^ 2 / 16 - 13 * (q : ℝ) * b / 50 ≤
          (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 10000 + 1 / 4 := by
      simpa only [M, q, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        hsquare
    dsimp [epsilon, gamma] at heM ⊢
    push_cast at hsquare' ⊢
    nlinarith
  have hconst : 0 ≤ eulerProduct⁻¹ * C.normalCount :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) C.normalCount_nonneg
  unfold preE7B6ExceptionalScalar
  dsimp only [q, M] at hs
  have hsource :
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (subgroupCount M : ℝ)) ≤
        C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs (by positivity))
      (mul_nonneg C.normalCount_nonneg (by positivity))
  have hpointUpper : 0 ≤ eulerProduct⁻¹ *
      (2 : ℝ) ^ (-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
        5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4) :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity)
  have hsourceUpper : 0 ≤
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
          (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) :=
    mul_nonneg (mul_nonneg C.normalCount_nonneg (by positivity))
      (by positivity)
  have hsourceLower : 0 ≤
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
          (subgroupCount M : ℝ)) := by
    have hsub : (0 : ℝ) ≤ subgroupCount M := by
      exact_mod_cast (subgroupCount_pos M).le
    exact mul_nonneg (mul_nonneg C.normalCount_nonneg (by positivity))
      (mul_nonneg (by positivity) hsub)
  have hrpow4 (a c d f : ℝ) :
      (2 : ℝ) ^ a * (2 : ℝ) ^ f *
          ((2 : ℝ) ^ c * (2 : ℝ) ^ d) =
        (2 : ℝ) ^ (a + f + c + d) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ (-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4)) *
        (C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
      exact mul_le_mul hpoint hsource hsourceLower hpointUpper
    _ ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ (-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4)) *
        (C.normalCount *
          (2 : ℝ) ^ (16 * gamma * (b : ℝ) ^ 2) *
          ((2 : ℝ) ^ (-((q : ℝ) * (13 / 50) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ hpointUpper
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfac C.normalCount_nonneg) (by positivity)
    _ = (eulerProduct⁻¹ * C.normalCount) *
        (2 : ℝ) ^
          ((-((b + 12 : ℕ) : ℝ) ^ 2 / 16 +
              5 * ((b + 12 : ℕ) : ℝ) / 8 + 1 / 4) +
            16 * gamma * (b : ℝ) ^ 2 +
            (-((q : ℝ) * (13 / 50) * b)) +
            (1 / 16 + epsilon) * (M : ℝ) ^ 2) := by
      rw [← hrpow4]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconst

/-- Package B6 as an actual mixed-catalogue action.  Its cold source sum is
the ordinary `4/3` row, while the retained rank tail supplies the exceptional
decay field. -/
noncomputable def PreE7EarlierLocalPackage.ofB6
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) :
    PreE7EarlierLocalPackage .b6 w i where
  certificate := .ofB6 C
  exceptional := fun hcoarse => by
    let h := eventually_atTop.mp
      (preE7B6ExceptionalScalar_eventually hcoarse C)
    let N : ℕ := Classical.choose h
    have hN := Classical.choose_spec h
    let K : ℝ := eulerProduct⁻¹ * C.normalCount
    refine
      { threshold := max N 1
        rate := 1 / 20000
        constant := K + 1
        rate_pos := by norm_num
        constant_pos := by
          have hK : 0 ≤ K := by
            dsimp [K]
            exact mul_nonneg (inv_nonneg.mpr euler_positive.le)
              C.normalCount_nonneg
          linarith
        bound := ?_ }
    intro b hb
    have hbN : N ≤ b := (le_max_left _ _).trans hb
    have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
    have hquad := hN b hbN
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (inv_nonneg.mpr euler_positive.le)
        C.normalCount_nonneg
    have hKle : K ≤ K + 1 := by linarith
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hexp : -((b : ℝ) ^ 2) / 20000 ≤
        -(1 / 20000 : ℝ) * b := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ b by positivity)
        (sub_nonneg.mpr hbR)]
    exact hquad.trans (mul_le_mul hKle
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (by positivity) (by linarith))
  exceptional_support := Or.inr (by
    rw [C.width_eq]
    norm_num)

/-- A B6 rank-tail certificate therefore supplies the exact action predicate
used by the mixed first-owner cover. -/
theorem preE7EarlierLocalFamilyAction_ofB6
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction .b6 w i :=
  ⟨.ofB6 C⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
