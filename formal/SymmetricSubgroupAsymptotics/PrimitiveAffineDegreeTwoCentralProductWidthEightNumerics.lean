import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductAnyWidthSource
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailDecay

/-!
# Width-eight numerical closure of the central four-pair rows

At width eight the normal-axis theorem leaves a main quotient moment of degree five, an
additive cold row of slope `3/5`, and one correlated binary-rank exceptional
term.  This file supplies the entry parameters and proves the exceptional
term decays exponentially from the published coarse subgroup estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7DegreeEightCentralProductSource

/-- The literal correlated source specialized only by its width-eight
permutation representation. -/
abbrev Data
    (U : PreE7NonPairActionClass 8) : Type 1 :=
  PreE7CentralProductRankTailData (preE7NonPairAction 8 U)

variable {U : PreE7NonPairActionClass 8}
  (C : Data U)

noncomputable def rawSummedSource :
    PreE7DegreeTwoPairSummedSource 8 U := C.pairSummedSource

def mainConstant : ℝ := PreE7CentralProductRankTailData.normalCount C
def coldConstant : ℝ := mainConstant C * C.lowerConstant
def fullConstant : ℝ := mainConstant C

theorem mainConstant_nonneg : 0 ≤ mainConstant C :=
  PreE7CentralProductRankTailData.normalCount_nonneg C

theorem coldConstant_nonneg : 0 ≤ coldConstant C :=
  mul_nonneg (mainConstant_nonneg C) C.lowerConstant_nonneg

theorem fullConstant_nonneg : 0 ≤ fullConstant C := mainConstant_nonneg C

def exceptionalEnvelope (b : ℕ) : ℝ := C.literalExceptionalEnvelope b

private theorem rankTail_degree_le_three_mul (b : ℕ) (hb : 1 ≤ b) :
    b + 2 * rankTail51Tilt b ≤ 3 * b := by
  unfold rankTail51Tilt
  omega

/-- After exact width-eight pointing and the finite epimorphism envelope, the
joint binary/index-three hot term retains a uniform quadratic deficit. -/
theorem exceptionalScalar_eventually
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∀ᶠ b : ℕ in atTop,
      (rawSummedSource C).exceptionalScalar b ≤
        (eulerProduct⁻¹ * (2 * fullConstant C)) *
          (2 : ℝ) ^ (-((b : ℝ) ^ 2) / 50000) := by
  let epsilon : ℝ := 1 / 10000000
  let gamma : ℝ := 1 / 10000000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by norm_num [gamma]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoarse epsilon hepsilon)
  filter_upwards [eventually_ge_atTop (max N 20000),
    eventually_succ_le_two_rpow hgamma] with b hb hsucc
  let q : ℕ := rankTail51Tilt b
  let M : ℕ := b + 2 * q
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hbLarge : 20000 ≤ b := (le_max_right _ _).trans hb
  have hbLargeR : (20000 : ℝ) ≤ b := by exact_mod_cast hbLarge
  have hb6 : 6 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hbM : b ≤ M := Nat.le_add_right _ _
  have hMN : N ≤ M := hbN.trans hbM
  have hM3 : M ≤ 3 * b := by
    simpa only [M, q] using rankTail_degree_le_three_mul b hb1
  have hM3R : (M : ℝ) ≤ 3 * (b : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ 9 * (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (b : ℝ) - M)]
  have hs := hN M hMN
  have hpoint0 := fusionHot_pointing_denominator_le b 4 (by omega)
  have hA : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
      (preE7NonPairAction 8 U : Set (Equiv.Perm (Fin 8)))) := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (preE7NonPairAction 8 U : Set (Equiv.Perm (Fin 8)))))
  have hpoint : growingQuotientNormalizedPointing b 8
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction 8 U : Set (Equiv.Perm (Fin 8)))) : ℝ) ≤
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
  have hsquare := y1RankTail_squareCompletion b
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
  have hconst : 0 ≤ eulerProduct⁻¹ * (2 * fullConstant C) :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le)
      (mul_nonneg (by norm_num) (fullConstant_nonneg C))
  unfold PreE7DegreeTwoPairSummedSource.exceptionalScalar
  change growingQuotientNormalizedPointing b 8
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction 8 U : Set (Equiv.Perm (Fin 8)))) : ℝ) *
      exceptionalEnvelope C b ≤ _
  dsimp only [q, M] at hs
  have hsource :
      exceptionalEnvelope C b ≤
        (2 * fullConstant C) * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
    unfold exceptionalEnvelope
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num) (fullConstant_nonneg C))
        (by positivity))
  have hpointUpper : 0 ≤ eulerProduct⁻¹ *
      (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
        5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4) :=
    mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity)
  have hsourceLower : 0 ≤ exceptionalEnvelope C b := by
    unfold exceptionalEnvelope
    have hsub : (0 : ℝ) ≤ subgroupCount M := by
      exact_mod_cast (subgroupCount_pos M).le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (fullConstant_nonneg C))
        (by positivity))
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
          (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4)) *
        ((2 * fullConstant C) * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
      exact mul_le_mul hpoint hsource hsourceLower hpointUpper
    _ ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ (-((b + 8 : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + 8 : ℕ) : ℝ) / 8 + 1 / 4)) *
        ((2 * fullConstant C) *
          (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ hpointUpper
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfac
          (mul_nonneg (by norm_num) (fullConstant_nonneg C)))
        (by positivity)
    _ = (eulerProduct⁻¹ * (2 * fullConstant C)) *
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

/-- The exceptional scalar in the local package. -/
noncomputable def exponentialExceptional
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ExponentialScalarBound (rawSummedSource C).exceptionalScalar := by
  let h := eventually_atTop.mp (exceptionalScalar_eventually C hcoarse)
  let N : ℕ := Classical.choose h
  have hN := Classical.choose_spec h
  let K : ℝ := eulerProduct⁻¹ * (2 * fullConstant C)
  refine
    { threshold := max N 1
      rate := 1 / 50000
      constant := K + 1
      rate_pos := by norm_num
      constant_pos := by
        have hK : 0 ≤ K := by
          dsimp [K]
          exact mul_nonneg (inv_nonneg.mpr euler_positive.le)
            (mul_nonneg (by norm_num) (fullConstant_nonneg C))
        linarith
      bound := ?_ }
  intro b hb
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hquad := hN b hbN
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (inv_nonneg.mpr euler_positive.le)
      (mul_nonneg (by norm_num) (fullConstant_nonneg C))
  have hKle : K ≤ K + 1 := by linarith
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hexp : -((b : ℝ) ^ 2) / 50000 ≤
      -(1 / 50000 : ℝ) * b := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ b by positivity)
      (sub_nonneg.mpr hbR)]
  exact hquad.trans (mul_le_mul hKle
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    (by positivity) (by linarith))

def centralProductDelta : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 5 8

def centralProductCutoff : ℝ :=
  (paddedComparatorDegree preE7CharacterRho 5 8 : ℝ) / 8 +
    centralProductDelta / 2

/-- The concrete additive numerical margin for the central-product row. -/
theorem centralProductEntryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho 8 5 0
      centralProductDelta centralProductCutoff centralProductCutoff
      (3 / 5) := by
  have hv : paddedComparatorDegree preE7CharacterRho 5 8 = 5 := by
    norm_num [paddedComparatorDegree, preE7CharacterRho, evenWidth,
      halfDegree]
  simpa [centralProductDelta, centralProductCutoff, hv] using
    (preE7Padded_entryParameters_withTail
      (w := 8) (v0 := 5) (eta := (0 : ℝ)) (theta := (3 / 5 : ℝ))
      (by norm_num) (by norm_num)
      (by norm_num [preE7CharacterRho, evenWidth, halfDegree])
      (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]))

/-- The physical local certificate keeps the quotient moment and the
additive cold row separate; this is the numerical margin that the generic
multiplicative `NumericalMargin` cannot express at width eight. -/
noncomputable def localCertificate :
    PreE7EarlierLocalCertificate .saprim 8 U where
  D := fun _ => mainConstant C
  T := fun _ => coldConstant C
  X := (rawSummedSource C).exceptionalScalar
  v := 5
  eta := 0
  delta := centralProductDelta
  cutoff := centralProductCutoff
  alpha := centralProductCutoff
  theta := 3 / 5
  alpha_eq := by simp
  D_nonneg := fun _ => mainConstant_nonneg C
  T_nonneg := fun _ => coldConstant_nonneg C
  local_bound := by
    intro b P hP _hPbroad
    simpa [rawSummedSource,
      PreE7CentralProductRankTailData.pairSummedSource,
      mainConstant, coldConstant, fullConstant,
      PreE7DegreeTwoPairSummedSource.exceptionalScalar] using
      ((rawSummedSource C).physical_normalized_bound b P hP
        centralProductDelta centralProductCutoff)

/-- Full local package, including the source-summed exceptional decay. -/
noncomputable def localPackage :
    PreE7EarlierLocalPackage .saprim 8 U where
  certificate := localCertificate C
  exceptional := exponentialExceptional C
  exceptional_support := Or.inr (by norm_num)

/-- Numerically complete package consumed by the ordinary earlier-owner
catalogue. -/
noncomputable def numericalPackage :
    PreE7EarlierNumericalPackage .saprim 8 U where
  package := localPackage C
  parameters := centralProductEntryParameters
  main_total_growth := .inr (.inl ⟨by norm_num, mainConstant C, 0,
    mainConstant_nonneg C, by
    intro b
    simp [localPackage, localCertificate]⟩)
  tail_total_growth := .inr ⟨by norm_num, coldConstant C, 0,
    coldConstant_nonneg C, by
      intro b
      simp [localPackage, localCertificate]⟩

/-- Final earlier-owner source for either central four-pair model. -/
noncomputable def rankTailOwnerSource :
    PreE7RankTailOwnerSourceData 8 U :=
  .ordinary .saprim (.package (numericalPackage C))

end PreE7DegreeEightCentralProductSource


end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
