import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailDecay
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailPhysical

/-!
# Quadratic decay of the Y1 index-three rank tail

The Y1 hot term carries one extra permutation beyond the B6 term, hence a
factor `(b!)^17`.  Its `b^2/40000` square-completion deficit still absorbs
that subquadratic factor and leaves a uniform quadratic decay.  The cold
term remains an ordinary width-eight row of slope `153/200`.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

def preE7Y1ExceptionalDelta : ℝ := preE7CharacterRho * 8 / 2

def preE7Y1ExceptionalCutoff : ℝ :=
  (1 : ℝ) / 8 + preE7Y1ExceptionalDelta / 2

/-- The hot Y1 scalar, with the index-three overgroup factor retained. -/
def preE7Y1ExceptionalScalar {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Y1RankTailCertificate w i) (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
    (C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
      ((Nat.factorial b : ℝ) *
        ((2 : ℝ) ^
            (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
          (subgroupCount
            (b + 2 * rankTail51Tilt b) : ℝ))))

/-- Y1 contributes its cold source estimate to the ordinary cold row and
keeps only the correlated index-three rank tail in the exceptional scalar. -/
noncomputable def PreE7EarlierLocalCertificate.ofY1
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Y1RankTailCertificate w i) :
    PreE7EarlierLocalCertificate .y1 w i where
  D := fun _ => 0
  T := fun b => C.coldConstant * (1 + b)
  X := preE7Y1ExceptionalScalar C
  v := 1
  eta := 0
  delta := preE7Y1ExceptionalDelta
  cutoff := preE7Y1ExceptionalCutoff
  alpha := preE7Y1ExceptionalCutoff
  theta := 153 / 200
  alpha_eq := by simp
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun b => mul_nonneg C.coldConstant_nonneg (by positivity)
  local_bound := by
    intro b P hP _hPbroad
    have h := C.physical_normalized_bound b P hP
    have hcold := growingQuotient_cold_identity (subgroupCount b : ℝ)
      b w (C.coldConstant * (1 + b))
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
      (153 / 200) 0
    rw [show (153 / 200 : ℝ) + 0 = 153 / 200 by ring] at hcold
    simp only [growingQuotientThreshold, zero_mul, Real.rpow_zero,
      mul_one] at hcold
    have hhotzero : growingQuotientHotKernel
        (fun n => (subgroupCount n : ℝ)) b w 1 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        0 preE7Y1ExceptionalDelta preE7Y1ExceptionalCutoff = 0 := by
      simp [growingQuotientHotKernel]
    have hcoldzero : fusionWidthColdKernel b w 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        preE7Y1ExceptionalCutoff = 0 := by
      simp [fusionWidthColdKernel]
    simp only [preE7Y1ExceptionalScalar, hhotzero, hcoldzero, zero_add]
    rw [ordinarySubgroupRatio, ← hcold]
    calc
      _ ≤ growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
          (C.coldConstant * (1 + b) *
                (2 : ℝ) ^ ((153 / 200 : ℝ) * b) *
                (subgroupCount b : ℝ) +
            C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
              ((Nat.factorial b : ℝ) *
                ((2 : ℝ) ^
                    (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
                  (subgroupCount
                    (b + 2 * rankTail51Tilt b) : ℝ)))) := h
      _ = _ := by ring

private theorem y1_rankTail_degree_le_three_mul (b : ℕ) (hb : 1 ≤ b) :
    b + 2 * rankTail51Tilt b ≤ 3 * b := by
  unfold rankTail51Tilt
  omega

/-- The exceptional Y1 term has a fixed quadratic deficit after the
`(b!)^17` fibre factor and the exact width-eight pointing are charged. -/
theorem preE7Y1ExceptionalScalar_eventually
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Y1RankTailCertificate w i) :
    ∀ᶠ b : ℕ in atTop,
      preE7Y1ExceptionalScalar C b ≤
        (eulerProduct⁻¹ * C.normalCount) *
          (2 : ℝ) ^ (-((b : ℝ) ^ 2) / 50000) := by
  have hw := C.width_eq
  subst w
  let epsilon : ℝ := 1 / 10000000
  let gamma : ℝ := 1 / 10000000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by norm_num [gamma]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoarse epsilon hepsilon)
  filter_upwards [eventually_ge_atTop (max N 8),
    eventually_succ_le_two_rpow hgamma] with b hb hsucc
  let q : ℕ := rankTail51Tilt b
  let M : ℕ := b + 2 * q
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hb8 : 8 ≤ b := (le_max_right _ _).trans hb
  have hb8R : (8 : ℝ) ≤ b := by exact_mod_cast hb8
  have hb1 : 1 ≤ b := by omega
  have hbM : b ≤ M := Nat.le_add_right _ _
  have hMN : N ≤ M := hbN.trans hbM
  have hM3 : M ≤ 3 * b := by
    simpa only [M, q] using y1_rankTail_degree_le_three_mul b hb1
  have hM3R : (M : ℝ) ≤ 3 * (b : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ 9 * (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (b : ℝ) - M)]
  have hs := hN M hMN
  have hpoint0 := fusionHot_pointing_denominator_le b 4 (by omega)
  have hA : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
      (preE7NonPairAction 8 i : Set (Equiv.Perm (Fin 8)))) := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (preE7NonPairAction 8 i : Set (Equiv.Perm (Fin 8)))))
  have hpoint : growingQuotientNormalizedPointing b 8
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction 8 i : Set (Equiv.Perm (Fin 8)))) : ℝ) ≤
      eulerProduct⁻¹ *
        (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4) := by
    unfold growingQuotientNormalizedPointing
    calc
      _ ≤ (((b + 8).factorial : ℝ) / (b.factorial : ℝ)) /
          exactBenchmark (b + 8) := by
        have hnum : 0 ≤ (((b + 8).factorial : ℝ) /
            (b.factorial : ℝ)) := by positivity
        have hbench : 0 < exactBenchmark (b + 8) :=
          exactBenchmark_pos (b + 8)
        apply div_le_div_of_nonneg_right _ hbench.le
        exact div_le_self hnum hA
      _ ≤ _ := hpoint0
  have hfacNat := factorial_le_succ_pow b
  have hfac : ((b.factorial : ℕ) : ℝ) ^ 17 ≤
      (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) := by
    have hfacR : ((b.factorial : ℕ) : ℝ) ≤
        (((b + 1 : ℕ) : ℝ) ^ b) := by exact_mod_cast hfacNat
    have hpow := pow_le_pow_left₀ (by positivity) hfacR 17
    have hsuccpow := pow_le_pow_left₀ (by positivity) hsucc (17 * b)
    calc
      ((b.factorial : ℕ) : ℝ) ^ 17 ≤
          ((((b + 1 : ℕ) : ℝ) ^ b) ^ 17) := hpow
      _ = (((b + 1 : ℕ) : ℝ) ^ (17 * b)) := by ring
      _ ≤ (((2 : ℝ) ^ (gamma * b)) ^ (17 * b)) := hsuccpow
      _ = (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring
  have hsquare := C.square_completion b
  have hexponent :
      (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4) +
        17 * gamma * (b : ℝ) ^ 2 +
        (-((q : ℝ) * (51 / 200) * b)) +
        (1 / 16 + epsilon) * (M : ℝ) ^ 2 ≤
          -((b : ℝ) ^ 2) / 50000 := by
    have heM : epsilon * (M : ℝ) ^ 2 ≤
        9 * epsilon * (b : ℝ) ^ 2 := by
      calc
        _ ≤ epsilon * (9 * (b : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hM2 hepsilon.le
        _ = _ := by ring
    have hsquare' :
        (M : ℝ) ^ 2 / 16 - (q : ℝ) * (51 / 200) * b ≤
          (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + 1 / 4 := by
      simpa only [M, q, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        hsquare
    dsimp [epsilon, gamma] at heM ⊢
    push_cast at hsquare' ⊢
    nlinarith
  have hconst : 0 ≤ eulerProduct⁻¹ * C.normalCount :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) C.normalCount_nonneg
  unfold preE7Y1ExceptionalScalar
  dsimp only [q, M] at hs
  have hsource :
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (subgroupCount M : ℝ))) ≤
        C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity))
      (mul_nonneg C.normalCount_nonneg (by positivity))
  have hpointUpper : 0 ≤ eulerProduct⁻¹ *
      (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
        5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4) :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity)
  have hsourceLower : 0 ≤
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((Nat.factorial b : ℝ) *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (subgroupCount M : ℝ))) := by
    have hsub : (0 : ℝ) ≤ subgroupCount M := by
      exact_mod_cast (subgroupCount_pos M).le
    exact mul_nonneg (mul_nonneg C.normalCount_nonneg (by positivity))
      (mul_nonneg (by positivity) (mul_nonneg (by positivity) hsub))
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
          (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4)) *
        (C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Nat.factorial b : ℝ) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)))) := by
      exact mul_le_mul hpoint hsource hsourceLower hpointUpper
    _ ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4)) *
        (C.normalCount *
          (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
      have hfac' : ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          (Nat.factorial b : ℝ) ≤
          (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) := by
        calc
          _ = ((Nat.factorial b : ℕ) : ℝ) ^ 17 := by ring
          _ ≤ _ := hfac
      apply mul_le_mul_of_nonneg_left _ hpointUpper
      calc
        _ = C.normalCount *
            (((Nat.factorial b : ℕ) : ℝ) ^ 16 *
              (Nat.factorial b : ℝ)) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by ring
        _ ≤ C.normalCount *
            (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfac' C.normalCount_nonneg)
            (by positivity)
    _ = (eulerProduct⁻¹ * C.normalCount) *
        (2 : ℝ) ^
          ((-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
              5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4) +
            17 * gamma * (b : ℝ) ^ 2 +
            (-((q : ℝ) * (51 / 200) * b)) +
            (1 / 16 + epsilon) * (M : ℝ) ^ 2) := by
      rw [← hrpow4]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconst

/-- A Y1 rank-tail certificate supplies the physical mixed-catalogue action
with a finite-support exceptional decay certificate. -/
noncomputable def PreE7EarlierLocalPackage.ofY1
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Y1RankTailCertificate w i) :
    PreE7EarlierLocalPackage .y1 w i where
  certificate := .ofY1 C
  exceptional := fun hcoarse => by
    let h := eventually_atTop.mp
      (preE7Y1ExceptionalScalar_eventually hcoarse C)
    let N : ℕ := Classical.choose h
    have hN := Classical.choose_spec h
    let K : ℝ := eulerProduct⁻¹ * C.normalCount
    refine
      { threshold := max N 1
        rate := 1 / 50000
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
    have hexp : -((b : ℝ) ^ 2) / 50000 ≤
        -(1 / 50000 : ℝ) * b := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ b by positivity)
        (sub_nonneg.mpr hbR)]
    exact hquad.trans (mul_le_mul hKle
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (by positivity) (by linarith))
  exceptional_support := Or.inr (by
    rw [C.width_eq]
    norm_num)

theorem preE7EarlierLocalFamilyAction_ofY1
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7Y1RankTailCertificate w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction .y1 w i :=
  ⟨.ofY1 C⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
