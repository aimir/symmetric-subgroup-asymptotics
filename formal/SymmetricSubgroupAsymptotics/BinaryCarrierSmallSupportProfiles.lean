import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportNormalized
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalProfileWeights
import SymmetricSubgroupAsymptotics.BinaryMixtureSmallSupportDecay

/-! The complete finite weighted profile sum at fixed original noncritical
half-support. Every summand is the actual model cardinality, with its own
original thirteen-color normalizer and multiplicity factorial denominator.
Only positive support and the stated support of the selected finite
profiles are hypotheses; no count or character-mark estimate is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportProfiles

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierOriginalSmallSupport

/-- Splitting out the original C4 color preserves the entire original
multiplicity function, including all distinct target colors. -/
theorem multiplicity_split (q : Target → ℕ) :
    multiplicity (q none) (fun t => q (some t)) = q := by
  funext t
  cases t <;> rfl

def support (q : Target → ℕ) : ℕ :=
  halfSupport (q none) (fun t => q (some t))

/-- The unlabelled actual subgroup count of the fixed original model. -/
def modelCount (p : CriticalProfile) (q : Target → ℕ) : ℝ :=
  (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p q (fun _ => True)) : ℝ)

/-- The occurrence enumeration is internal and does not change the original
profile or introduce a multiplicity into its subgroup count. -/
theorem modelCount_div_gaussian_le (p : CriticalProfile) (q : Target → ℕ)
    (R C : ℕ) (hp : p.rank = R) (hq : support q = C) (hC : 0 < C) :
    modelCount p q / (binaryGaussianSum (R+C) : ℝ) ≤
      BinaryCarrierSmallSupportNormalized.bound R C := by
  let m : CarrierTarget → ℕ := fun t => q (some t)
  let occurrences : Fin (Fintype.card (Σ t, Fin (m t))) ≃ (Σ t, Fin (m t)) :=
    (Fintype.equivFin (Σ t, Fin (m t))).symm
  have hc : 0 < halfSupport (q none) m := by
    change 0 < support q
    simpa only [hq] using hC
  have h := BinaryCarrierSmallSupportNormalized.modelFamily_card_div_gaussian_le
    (q none) m occurrences p hc (fun _ => True)
  change (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p
    (multiplicity (q none) (fun t => q (some t))) (fun _ => True)) : ℝ) /
      (binaryGaussianSum (p.rank + support q) : ℝ) ≤
        BinaryCarrierSmallSupportNormalized.bound p.rank (support q) at h
  rw [multiplicity_split, hp, hq] at h
  exact h

theorem modelCount_le (p : CriticalProfile) (q : Target → ℕ)
    (R C : ℕ) (hp : p.rank = R) (hq : support q = C) (hC : 0 < C) :
    modelCount p q ≤ (binaryGaussianSum (R+C) : ℝ) *
      BinaryCarrierSmallSupportNormalized.bound R C := by
  have hG : (0 : ℝ) < binaryGaussianSum (R+C) := by
    exact_mod_cast binaryGaussianSum_pos (R+C)
  have h := (div_le_iff₀ hG).mp (modelCount_div_gaussian_le p q R C hp hq hC)
  simpa only [mul_comm] using h

/-- Sum every selected noncritical profile and every critical profile of
rank R, retaining the entire original critical coefficient shift C. -/
theorem weighted_profile_sum_le (R C : ℕ) (hC : 0 < C)
    (S : CriticalProfile → Finset (Target → ℕ))
    (hS : ∀ p ∈ criticalProfiles R, ∀ q ∈ S p, support q = C) :
    (∑ p : criticalProfiles R, ∑ q ∈ S p.1,
      modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q) /
        ((criticalCoefficient (R+C) : ℝ) * (binaryGaussianSum (R+C) : ℝ)) ≤
      Real.exp 13 * (2 * ((R+C : ℕ) : ℝ))^C *
        BinaryCarrierSmallSupportNormalized.bound R C := by
  apply original_shifted_profile_count_sum_le R C S modelCount
    (BinaryCarrierSmallSupportNormalized.bound R C)
  · unfold BinaryCarrierSmallSupportNormalized.bound
    positivity [euler_positive]
  · intro p hp q hq
    exact modelCount_le p q R C ((mem_criticalProfiles R p).mp hp) (hS p hp q hq) hC

/-- Uniform decay of the complete finite profile-weight sum at each
positive support below the explicit physical cutoff. This is a profile
sum, not an assertion that these profiles cover every physical subgroup. -/
theorem eventually_weighted_profile_sum_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R C : ℕ, R+C=n → 0<C →
      (C : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      ∀ S : CriticalProfile → Finset (Target → ℕ),
      (∀ p ∈ criticalProfiles R, ∀ q ∈ S p, support q = C) →
      (∑ p : criticalProfiles R, ∑ q ∈ S p.1,
        modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q) /
          ((criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ)) ≤
            (2 : ℝ)^(-(n : ℝ)/4) := by
  let A : ℝ := Real.exp 13 * 4 * (eulerProduct⁻¹)^6
  have hA : 0 < A := by dsimp [A]; positivity [euler_positive]
  filter_upwards [BinaryMixtureNumerics.eventually_small_support_prefactor_bound A hA 4]
    with n hn
  intro R C hRC hC hcut S hS
  have hsum := weighted_profile_sum_le R C hC S hS
  have hreal : (R : ℝ)+(C : ℝ)=(n : ℝ) := by exact_mod_cast hRC
  calc
    _ ≤ Real.exp 13 * (2 * ((R+C : ℕ) : ℝ))^C *
        BinaryCarrierSmallSupportNormalized.bound R C := by
      simpa only [hRC] using hsum
    _ = A * ((n : ℝ)+1)^4 * (2*(n : ℝ))^C *
        (2 : ℝ)^(-(n : ℝ)/2+1/2+(211/192)*(C : ℝ)^2+(14/3)*C+49/3) := by
      simp only [BinaryCarrierSmallSupportNormalized.bound, hRC, hreal]
      dsimp [A]
      ring
    _ ≤ _ := hn C hcut

end SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportProfiles
