import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportProfiles
import SymmetricSubgroupAsymptotics.OrbitProfileUpperUnion

/-! The literal physical union of all original thirteen-color profiles
at one positive noncritical support. The finite profile box is proved
complete from the actual positive physical scales. Possible overlap of
presentations is handled by a union upper bound, with original normalizer
weights; no separation, transitivity or unique-presentation hypothesis
is needed here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportPhysical

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierOriginalSmallSupport
open BinaryCarrierSmallSupportProfiles

theorem originalScale_pos (t : CarrierTarget) :
    1 ≤ BinaryCarrierOriginalActions.factorScaleNat t := by
  cases t <;> norm_num [BinaryCarrierOriginalActions.factorScaleNat]

theorem carrierMultiplicity_le_scale (m : CarrierTarget → ℕ) (t : CarrierTarget) :
    m t ≤ BinaryCarrierOriginalActions.scale m := by
  calc
    _ = m t * 1 := by simp
    _ ≤ m t * BinaryCarrierOriginalActions.factorScaleNat t :=
      Nat.mul_le_mul_left _ (originalScale_pos t)
    _ ≤ _ := Finset.single_le_sum
      (f := fun s => m s * BinaryCarrierOriginalActions.factorScaleNat s)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)

/-- Every original multiplicity is bounded by the actual half-support. -/
theorem multiplicity_le_support (q : Target → ℕ) (t : Target) : q t ≤ support q := by
  cases t with
  | none => change q none ≤ 2*q none+4*BinaryCarrierOriginalActions.scale _; omega
  | some t =>
      have h := carrierMultiplicity_le_scale (fun t => q (some t)) t
      change q (some t) ≤ 2*q none+4*BinaryCarrierOriginalActions.scale _
      omega

def profilesAtSupport (C : ℕ) : Finset (Target → ℕ) :=
  (Fintype.piFinset (fun _ : Target => Finset.range (C+1))).filter (fun q => support q=C)

/-- This is all original multiplicity functions of support C, not merely
a selected list or a family accepted through stored numerical profiles. -/
@[simp] theorem mem_profilesAtSupport (C : ℕ) (q : Target → ℕ) :
    q ∈ profilesAtSupport C ↔ support q=C := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun t => Finset.mem_range.mpr ?_), h⟩
    have ht := multiplicity_le_support q t
    omega

abbrev ProfileIndex (R C : ℕ) := (criticalProfiles R) × (profilesAtSupport C)

def profileMultiplicity (R C : ℕ) (i : ProfileIndex R C) :
    CriticalActionKind ⊕ Target → ℕ :=
  BinaryCarrierMixedProfile.multiplicity i.1.1 i.2.1

def profilePredicate (R C : ℕ) (i : ProfileIndex R C) :=
  OrbitProfileFull (m := profileMultiplicity R C i)
    (BinaryCarrierMixedProfile.action points action) 1

/-- Membership asserts an actual full original action chart on X. -/
abbrev PhysicalFamily (R C : ℕ) (X : Type*) :=
  AssembledOrbitProfilesOn (profileMultiplicity R C) (profilePredicate R C) X

theorem physicalDegree (R C : ℕ) (i : ProfileIndex R C) :
    ∑ t, profileMultiplicity R C i t *
      Fintype.card (BinaryCarrierMixedProfile.points points t) = 2*(R+C) := by
  have hp : i.1.1.rank=R := (mem_criticalProfiles R i.1.1).mp i.1.2
  have hq : support i.2.1=C := (mem_profilesAtSupport C i.2.1).mp i.2.2
  have h := physicalDegree_eq i.1.1 (i.2.1 none) (fun t => i.2.1 (some t))
  rw [multiplicity_split] at h
  change BinaryCarrierMixedProfile.physicalDegree points i.1.1 i.2.1 = _
  rw [h, hp]
  let s : ℕ := BinaryCarrierOriginalActions.scale (fun t => i.2.1 (some t))
  change 2*(i.2.1 none)+4*s=C at hq
  change 2*R+4*(i.2.1 none)+8*s=2*(R+C)
  omega

def weightedSum (R C : ℕ) : ℝ :=
  ∑ p : criticalProfiles R, ∑ q ∈ profilesAtSupport C,
    modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q

/-- Every original physical subgroup is counted by at least one profile;
the upper sum retains each profile's original denominator. -/
theorem card_le_factorial_sum (R C : ℕ) :
    (Nat.card (PhysicalFamily R C (Fin (2*(R+C)))) : ℝ) ≤
      ((2*(R+C)).factorial : ℝ) * weightedSum R C := by
  have h := assembledOrbitProfilesOn_fin_card_le_real
    (profileMultiplicity R C) (BinaryCarrierMixedProfile.action points action)
    (profilePredicate R C) (2*(R+C)) (physicalDegree R C)
    (fun i => orbitProfileFull_family_natural (profileMultiplicity R C i)
      (BinaryCarrierMixedProfile.action points action))
  apply h.trans_eq
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  simpa only [profileMultiplicity, profilePredicate, modelCount,
    BinaryCarrierMixedProfile.ModelFamily, and_true,
    BinaryCarrierMixedProfile.originalDenominator] using
      (Finset.sum_coe_sort (profilesAtSupport C) (fun q =>
        modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q))

private theorem benchmark_even (n : ℕ) :
    exactBenchmark (2*n) = ((2*n).factorial : ℝ) *
      (binaryGaussianSum n : ℝ) * (criticalCoefficient n : ℝ) := by
  simp [exactBenchmark, halfDegree, parityCoefficient, parity]

/-- The physical factorial cancels against the same exact benchmark. -/
theorem card_div_benchmark_le_weightedSum (R C : ℕ) :
    (Nat.card (PhysicalFamily R C (Fin (2*(R+C)))) : ℝ) / exactBenchmark (2*(R+C)) ≤
      weightedSum R C /
        ((criticalCoefficient (R+C) : ℝ) * (binaryGaussianSum (R+C) : ℝ)) := by
  have hf : (0 : ℝ) < ((2*(R+C)).factorial : ℝ) := by positivity
  have hc : (0 : ℝ) < criticalCoefficient (R+C) := by
    exact_mod_cast criticalCoefficient_pos (R+C)
  have hg : (0 : ℝ) < binaryGaussianSum (R+C) := by
    exact_mod_cast binaryGaussianSum_pos (R+C)
  calc
    _ ≤ (((2*(R+C)).factorial : ℝ) * weightedSum R C) /
        exactBenchmark (2*(R+C)) :=
      div_le_div_of_nonneg_right (card_le_factorial_sum R C) (exactBenchmark_pos _).le
    _ = _ := by
      rw [benchmark_even]
      field_simp [hf.ne', hc.ne', hg.ne']
      <;> ring

/-- Fixed-support physical union bound, with no count or coverage input. -/
theorem card_div_benchmark_le (R C : ℕ) (hC : 0<C) :
    (Nat.card (PhysicalFamily R C (Fin (2*(R+C)))) : ℝ) / exactBenchmark (2*(R+C)) ≤
      Real.exp 13 * (2 * ((R+C : ℕ) : ℝ))^C *
        BinaryCarrierSmallSupportNormalized.bound R C := by
  apply (card_div_benchmark_le_weightedSum R C).trans
  exact weighted_profile_sum_le R C hC (fun _ => profilesAtSupport C)
    (fun _ _ q hq => (mem_profilesAtSupport C q).mp hq)

/-- Uniform decay of the literal physical union at each positive small
support. Summing different supports remains a separate finite union. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R C : ℕ, R+C=n → 0<C →
      (C : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      (Nat.card (PhysicalFamily R C (Fin (2*(R+C)))) : ℝ) / exactBenchmark (2*(R+C)) ≤
        (2 : ℝ)^(-(n : ℝ)/4) := by
  filter_upwards [eventually_weighted_profile_sum_le] with n hn
  intro R C hRC hC hcut
  apply (card_div_benchmark_le_weightedSum R C).trans
  simpa only [weightedSum, hRC] using hn R C hRC hC hcut (fun _ => profilesAtSupport C)
    (fun _ _ q hq => (mem_profilesAtSupport C q).mp hq)

end SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportPhysical
