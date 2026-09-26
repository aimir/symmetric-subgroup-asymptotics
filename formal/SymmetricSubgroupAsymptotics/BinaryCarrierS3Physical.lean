import SymmetricSubgroupAsymptotics.BinaryCarrierS3Actions
import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
import SymmetricSubgroupAsymptotics.SingletonBenchmark

/-! Actual S3-marked physical bins with their original normalizer six.
Only a forgetful union is used, so distinct chart presentations may overlap.
The odd benchmark retains its nonnegative additional marker coefficient. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Physical

open BinaryCarrierS3Actions

abbrev ProfileIndex := BinaryCarrierParameterProfiles.ProfileIndex

def profileMultiplicity (R a T : ℕ) (i : ProfileIndex R a T) :=
  multiplicity i.1.1 i.2.1

def profilePredicate (R a T : ℕ) (i : ProfileIndex R a T) :=
  OrbitProfileFull (m := profileMultiplicity R a T i) action 1

abbrev PhysicalFamily (R a T : ℕ) (X : Type*) :=
  AssembledOrbitProfilesOn (profileMultiplicity R a T) (profilePredicate R a T) X

def modelCount (p : CriticalProfile) (q : Target → ℕ) : ℝ := Nat.card (ModelFamily p q)

def weightedSum (R a T : ℕ) : ℝ :=
  ∑ p : criticalProfiles R, ∑ q ∈ BinaryCarrierParameterProfiles.profilesAtParameters a T,
    modelCount p.1 q / (6 * BinaryCarrierMixedProfile.originalDenominator
      BinaryCarrierOriginalCyclicFourHall.points BinaryCarrierOriginalCyclicFourHall.action p.1 q)

theorem weightedSum_nonneg (R a T : ℕ) : 0 ≤ weightedSum R a T := by
  unfold weightedSum modelCount BinaryCarrierMixedProfile.originalDenominator
  positivity

theorem physicalDegree (R a T : ℕ) (i : ProfileIndex R a T) :
    ∑ t, profileMultiplicity R a T i t * Fintype.card (points t) =
      2*(R+2*a+4*T+1)+1 := by
  have hp := (mem_criticalProfiles R i.1.1).mp i.1.2
  have hq := BinaryCarrierParameterProfiles.support_eq a T i.2
  change (∑ t, multiplicity i.1.1 i.2.1 t * Fintype.card (points t)) = _
  rw [BinaryCarrierS3Actions.physicalDegree, hp, hq]
  omega

/-- The full original labelled count, including all original profiles
in this bin, has precisely the S3 divisor six in its upper sum. -/
theorem card_le_factorial_sum (R a T : ℕ) :
    (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T+1)+1))) : ℝ) ≤
      ((2*(R+2*a+4*T+1)+1).factorial : ℝ) * weightedSum R a T := by
  have h := assembledOrbitProfilesOn_fin_card_le_real
    (profileMultiplicity R a T) action (profilePredicate R a T)
    (2*(R+2*a+4*T+1)+1) (physicalDegree R a T)
    (fun i => orbitProfileFull_family_natural (profileMultiplicity R a T i) action)
  apply h.trans_eq
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  change (∑ q : BinaryCarrierParameterProfiles.profilesAtParameters a T,
    modelCount p.1 q.1 / originalDenominator p.1 q.1) = _
  simp_rw [originalDenominator_eq]
  exact Finset.sum_coe_sort (BinaryCarrierParameterProfiles.profilesAtParameters a T)
    (fun q => modelCount p.1 q / (6 * BinaryCarrierMixedProfile.originalDenominator
      BinaryCarrierOriginalCyclicFourHall.points BinaryCarrierOriginalCyclicFourHall.action p.1 q))

theorem oddBenchmark_lower (n : ℕ) :
    ((2*n+1).factorial : ℝ) *
      ((criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ)) ≤ exactBenchmark (2*n+1) := by
  have he : exactBenchmark (2*n) = ((2*n).factorial : ℝ) *
      (binaryGaussianSum n : ℝ) * (criticalCoefficient n : ℝ) := by
    simp [exactBenchmark, halfDegree, parityCoefficient, parity]
  calc
    _ = ((2*n+1 : ℕ) : ℝ) * exactBenchmark (2*n) := by
      rw [he, Nat.factorial_succ, Nat.cast_mul]
      ring
    _ ≤ _ := exactBenchmark_odd_ge_singleton_even n

/-- Normalize at the contracted half-degree R+2a+4T+1, retaining the
entire original odd factorial and the original S3 profile weight. -/
theorem card_div_benchmark_le_weightedSum (R a T : ℕ) :
    (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T+1)+1))) : ℝ) /
      exactBenchmark (2*(R+2*a+4*T+1)+1) ≤
        weightedSum R a T / ((criticalCoefficient (R+2*a+4*T+1) : ℝ) *
          (binaryGaussianSum (R+2*a+4*T+1) : ℝ)) := by
  let n := R+2*a+4*T+1
  have hf : (0 : ℝ) < ((2*n+1).factorial : ℝ) := by positivity
  have hc : (0 : ℝ) < criticalCoefficient n := by exact_mod_cast criticalCoefficient_pos n
  have hg : (0 : ℝ) < binaryGaussianSum n := by exact_mod_cast binaryGaussianSum_pos n
  calc
    _ ≤ (((2*n+1).factorial : ℝ) * weightedSum R a T) / exactBenchmark (2*n+1) :=
      div_le_div_of_nonneg_right (card_le_factorial_sum R a T) (exactBenchmark_pos _).le
    _ ≤ (((2*n+1).factorial : ℝ) * weightedSum R a T) /
        (((2*n+1).factorial : ℝ) * ((criticalCoefficient n : ℝ)*(binaryGaussianSum n : ℝ))) :=
      div_le_div_of_nonneg_left (mul_nonneg hf.le (weightedSum_nonneg R a T))
        (mul_pos hf (mul_pos hc hg)) (oddBenchmark_lower n)
    _ = _ := by
      dsimp only [n] at hf hc hg ⊢
      field_simp [hf.ne', hc.ne', hg.ne']

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Physical
