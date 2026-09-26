import SymmetricSubgroupAsymptotics.BinaryCarrierS3Physical
import SymmetricSubgroupAsymptotics.BinaryCarrierS3Model
import SymmetricSubgroupAsymptotics.BinaryCarrierS3Weights
import SymmetricSubgroupAsymptotics.BinaryCarrierWeightedMixture

/-! Decay of the actual original S3-marked profile bin. Model contraction
is an exact cardinal identity. The original marker divisor six is retained
while critical rank R is reindexed into R+1. The weighted estimate is used
before the physical upper assembly, never inferred from a physical union.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Decay

open BinaryCarrierOriginalCyclicFourHall

theorem modelCount_eq_addC2 (p : CriticalProfile) (q : Target → ℕ) :
    BinaryCarrierS3Physical.modelCount p q =
      BinaryCarrierSmallSupportProfiles.modelCount p.addC2 q :=
  BinaryCarrierS3Model.model_count p q

/-- The original S3 factor is exactly six. Every carrier profile q and
its normalizers are unchanged; the even sum has critical rank R+1. -/
theorem weightedSum_le (R a T : ℕ) :
    BinaryCarrierS3Physical.weightedSum R a T ≤
      (((R+1 : ℕ) : ℝ)/3) * BinaryCarrierParameterProfiles.weightedSum (R+1) a T := by
  have h := BinaryCarrierS3Weights.originalDenominator_s3_sum_le points action R
    (BinaryCarrierParameterProfiles.profilesAtParameters a T)
    BinaryCarrierSmallSupportProfiles.modelCount
    (fun _ _ _ _ => Nat.cast_nonneg _)
  simpa only [BinaryCarrierS3Physical.weightedSum, modelCount_eq_addC2,
    BinaryCarrierParameterProfiles.weightedSum] using h

/-- The sharp original occurrence factor remains visible before its
polynomial relaxation in the full half-degree N. -/
theorem eventually_weightedSum_div_le_factor :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ R a T : ℕ,
      R+2*a+4*T+1=N → 0<2*a+4*T →
      BinaryCarrierS3Physical.weightedSum R a T /
        ((criticalCoefficient N : ℝ) * (binaryGaussianSum N : ℝ)) ≤
          (((R+1 : ℕ) : ℝ)/3) * (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  filter_upwards [BinaryCarrierWeightedMixture.eventually_weightedSum_div_le] with N hN
  intro R a T hdegree hsupport
  have hshift : (R+1)+2*a+4*T=N := by omega
  have hden : 0 ≤ (criticalCoefficient N : ℝ) * (binaryGaussianSum N : ℝ) :=
    mul_nonneg (by exact_mod_cast (criticalCoefficient_pos N).le)
      (by exact_mod_cast (binaryGaussianSum_pos N).le)
  calc
    _ ≤ ((((R+1 : ℕ) : ℝ)/3) *
        BinaryCarrierParameterProfiles.weightedSum (R+1) a T) /
          ((criticalCoefficient N : ℝ) * (binaryGaussianSum N : ℝ)) :=
      div_le_div_of_nonneg_right (weightedSum_le R a T) hden
    _ = (((R+1 : ℕ) : ℝ)/3) *
        (BinaryCarrierParameterProfiles.weightedSum (R+1) a T /
          ((criticalCoefficient N : ℝ) * (binaryGaussianSum N : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hN (R+1) a T hshift hsupport) (by positivity)

/-- A uniform polynomial factor in the complete half-degree, with the
original positive-support weighted bin and its shifted coefficient. -/
theorem eventually_weightedSum_div_le :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ R a T : ℕ,
      R+2*a+4*T+1=N → 0<2*a+4*T →
      BinaryCarrierS3Physical.weightedSum R a T /
        ((criticalCoefficient N : ℝ) * (binaryGaussianSum N : ℝ)) ≤
          ((N : ℝ)+1) * (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  filter_upwards [eventually_weightedSum_div_le_factor] with N hN
  intro R a T hdegree hsupport
  apply (hN R a T hdegree hsupport).trans
  have hRN : ((R+1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show R+1 ≤ N by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

/-- Every actual original labelled S3-marked bin is small at its odd
physical degree. The original factorial, normalizer six, and complete
odd benchmark have already been retained by the physical upper assembly. -/
theorem eventually_physical_card_div_le :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ R a T : ℕ,
      R+2*a+4*T+1=N → 0<2*a+4*T →
      (Nat.card (BinaryCarrierS3Physical.PhysicalFamily R a T (Fin (2*N+1))) : ℝ) /
        exactBenchmark (2*N+1) ≤
          ((N : ℝ)+1) * (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  filter_upwards [eventually_weightedSum_div_le] with N hN
  intro R a T hdegree hsupport
  have hphysical := BinaryCarrierS3Physical.card_div_benchmark_le_weightedSum R a T
  rw [hdegree] at hphysical
  exact hphysical.trans (hN R a T hdegree hsupport)

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Decay
