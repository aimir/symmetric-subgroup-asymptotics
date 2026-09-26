import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourReserve
import SymmetricSubgroupAsymptotics.BinaryMixtureCarrierDecay
import SymmetricSubgroupAsymptotics.GaussianUniformLower

/-! Actual original profile bins in the large-carrier regime. The source
occurrence bound is proved from original multiplicities and physical scales.
All model counts are actual cardinalities, and all profile weights retain
the original thirteen action normalizers and occurrence factorials. No
counting estimate is supplied as a premise.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryCarrierReserveProfiles

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierSmallSupportProfiles
open BinaryCarrierParameterProfiles

/-- Every separate original carrier occurrence has physical scale at
least one, even when several original colors use the same source master. -/
theorem carrier_occurrence_card_le_scale (m : CarrierTarget → ℕ) :
    Fintype.card (Σ t, Fin (m t)) ≤ BinaryCarrierOriginalActions.scale m := by
  simp only [Fintype.card_sigma, Fintype.card_fin, BinaryCarrierOriginalActions.scale]
  apply Finset.sum_le_sum
  intro t _
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (m t) (BinaryCarrierSmallSupportPhysical.originalScale_pos t)

/-- The common scalar envelope is independent of both original profiles. -/
def envelope (n T : ℕ) : ℝ :=
  (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
    BinaryCarrierReserveEnvelope.constant 12*(n : ℝ)*Real.log ((n : ℝ)+2))

theorem envelope_nonneg (n T : ℕ) : 0 ≤ envelope n T := by
  unfold envelope
  positivity

/-- Derive the common model estimate from the actual original source
word; its length is bounded internally and is never a count of colors. -/
theorem modelCount_le_envelope (p : CriticalProfile) (q : Target → ℕ)
    (R a T : ℕ) (hp : p.rank = R) (hq : q ∈ profilesAtParameters a T)
    (hN : 1 ≤ R+2*a+4*T) :
    modelCount p q ≤ envelope (R+2*a+4*T) T := by
  obtain ⟨hqa, hqT⟩ := (mem_profilesAtParameters a T q).mp hq
  let m : CarrierTarget → ℕ := fun t => q (some t)
  let L : ℕ := Fintype.card (Σ t, Fin (m t))
  let occurrences : Fin L ≃ (Σ t, Fin (m t)) :=
    (Fintype.equivFin (Σ t, Fin (m t))).symm
  have hscale : BinaryCarrierOriginalActions.scale m = T := hqT
  have hL : L ≤ T := by
    rw [← hscale]
    exact carrier_occurrence_card_le_scale m
  have hmodel := BinaryCarrierOriginalCyclicFourReserve.modelFamily_card_le_reserve
    p (q none) m occurrences (fun _ => True)
  change (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p
    (multiplicity (q none) (fun t => q (some t))) (fun _ => True)) : ℝ) ≤
      BinaryCarrierWord.terminalProductReserve (p.abelianRank+2*(q none))
        (criticalProfileNonabelianChoice p) 12 L
          (BinaryCarrierOriginalActions.scale m : ℝ) at hmodel
  rw [multiplicity_split, hqa, hscale] at hmodel
  have hrank : criticalProductRank (p.abelianRank+2*a)
      (criticalProfileNonabelianChoice p) = R+2*a := by
    calc
      _ = criticalProductRank p.abelianRank (criticalProfileNonabelianChoice p) + 2*a := by
        unfold criticalProductRank
        omega
      _ = _ := by rw [criticalProfile_product_rank, hp]
  have htotal : (criticalProductRank (p.abelianRank+2*a)
      (criticalProfileNonabelianChoice p) : ℝ)+4*T = ((R+2*a+4*T : ℕ) : ℝ) := by
    rw [hrank]
    push_cast
    ring
  have henv := BinaryCarrierReserveEnvelope.terminalProductReserve_le 12
    (p.abelianRank+2*a) (criticalProfileNonabelianChoice p) L (T : ℝ)
    (by positivity) (by exact_mod_cast hL) (by
      rw [htotal]
      exact_mod_cast hN)
  rw [htotal] at henv
  exact hmodel.trans henv

/-- Complete weighted profile sum at fixed a,T. The critical coefficient
shift and the parity-uniform Gaussian lower bound are both explicit. -/
theorem weightedSum_div_le_envelope (R a T : ℕ) (hN : 1 ≤ R+2*a+4*T) :
    weightedSum R a T /
      ((criticalCoefficient (R+2*a+4*T) : ℝ) * (binaryGaussianSum (R+2*a+4*T) : ℝ)) ≤
        (Real.exp 13 * (2*((R+2*a+4*T : ℕ) : ℝ))^(2*a+4*T) *
          envelope (R+2*a+4*T) T) /
          (eulerProduct*(2 : ℝ)^(((R+2*a+4*T : ℕ) : ℝ)^2/4-1/4)) := by
  let n : ℕ := R+2*a+4*T
  let D : ℝ := eulerProduct*(2 : ℝ)^((n : ℝ)^2/4-1/4)
  have hD : 0 < D := by dsimp [D]; positivity [euler_positive]
  have hM : 0 ≤ envelope n T / D := div_nonneg (envelope_nonneg n T) hD.le
  have hindex : R+(2*a+4*T) = n := by dsimp [n]; omega
  have hsum := original_shifted_profile_count_sum_le R (2*a+4*T)
    (fun _ => profilesAtParameters a T) modelCount (envelope n T / D) hM (by
      intro p hp q hq
      have hcount := modelCount_le_envelope p q R a T
        ((mem_criticalProfiles R p).mp hp) hq hN
      have hG : D ≤ (binaryGaussianSum n : ℝ) := binaryGaussianSum_quadratic_lower n
      calc
        _ ≤ envelope n T := hcount
        _ = D * (envelope n T / D) := by field_simp [hD.ne']
        _ ≤ (binaryGaussianSum n : ℝ) * (envelope n T / D) :=
          mul_le_mul_of_nonneg_right hG hM
        _ = _ := by rw [hindex])
  change weightedSum R a T /
    ((criticalCoefficient (R+(2*a+4*T)) : ℝ) * (binaryGaussianSum (R+(2*a+4*T)) : ℝ)) ≤
      Real.exp 13 * (2*((R+(2*a+4*T) : ℕ) : ℝ))^(2*a+4*T) * (envelope n T / D) at hsum
  rw [hindex] at hsum
  calc
    _ ≤ Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) * (envelope n T / D) := hsum
    _ = _ := by dsimp [n, D]; ring

/-- The same pointwise estimate for the actual original labelled union.
No uniqueness of profile witnesses and no normalizer replacement is used. -/
theorem card_div_benchmark_le_envelope (R a T : ℕ) (hN : 1 ≤ R+2*a+4*T) :
    (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) : ℝ) /
      exactBenchmark (2*(R+2*a+4*T)) ≤
        (Real.exp 13 * (2*((R+2*a+4*T : ℕ) : ℝ))^(2*a+4*T) *
          envelope (R+2*a+4*T) T) /
          (eulerProduct*(2 : ℝ)^(((R+2*a+4*T : ℕ) : ℝ)^2/4-1/4)) :=
  (card_div_benchmark_le_weightedSum R a T).trans (weightedSum_div_le_envelope R a T hN)

/-- Uniform normalized weighted-bin decay in the large-carrier regime. -/
theorem eventually_weightedSum_div_le :
    ∀ᶠ n : ℕ in atTop, ∀ R a T : ℕ, R+2*a+4*T=n → a<140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) →
      weightedSum R a T / ((criticalCoefficient n : ℝ)*(binaryGaussianSum n : ℝ)) ≤
        (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  filter_upwards [BinaryMixtureNumerics.eventually_normalized_carrier_with_gaussian_lower
      eulerProduct euler_positive 0 (BinaryCarrierReserveEnvelope.constant 12)
      (BinaryCarrierReserveEnvelope.constant_nonneg 12),
    eventually_ge_atTop 1] with n hn hn1
  intro R a T hN ha hcut
  have hbound := weightedSum_div_le_envelope R a T (by omega)
  rw [hN] at hbound
  apply hbound.trans
  simpa only [envelope, pow_zero, mul_one] using hn R a T hN.symm ha hcut

/-- The actual original physical bin is exponentially negligible. This
is confined to the thirteen specified colors and asserts no global binary
classification or owner coverage. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in atTop, ∀ R a T : ℕ, R+2*a+4*T=n → a<140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) →
      (Nat.card (PhysicalFamily R a T (Fin (2*n))) : ℝ) / exactBenchmark (2*n) ≤
        (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  filter_upwards [eventually_weightedSum_div_le] with n hn
  intro R a T hN ha hcut
  have hphysical := card_div_benchmark_le_weightedSum R a T
  rw [hN] at hphysical
  exact hphysical.trans (hn R a T hN ha hcut)

end SymmetricSubgroupAsymptotics.BinaryCarrierReserveProfiles
