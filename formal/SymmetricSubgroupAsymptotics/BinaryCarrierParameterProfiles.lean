import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportPhysical

/-! Complete original profile bins with fixed C4 multiplicity a and
carrier scale T. The same finite physical union and exact denominator
are used by both the Hall and reserve regimes. No counting estimate is
part of the bin definition or of its completeness proof. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierSmallSupportProfiles

def profilesAtParameters (a T : ℕ) : Finset (Target → ℕ) :=
  (BinaryCarrierSmallSupportPhysical.profilesAtSupport (2*a+4*T)).filter
    (fun q => q none=a ∧ BinaryCarrierOriginalActions.scale (fun t => q (some t))=T)

@[simp] theorem mem_profilesAtParameters (a T : ℕ) (q : Target → ℕ) :
    q ∈ profilesAtParameters a T ↔
      q none=a ∧ BinaryCarrierOriginalActions.scale (fun t => q (some t))=T := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨(BinaryCarrierSmallSupportPhysical.mem_profilesAtSupport _ _).mpr ?_, h⟩
    change 2*q none+4*BinaryCarrierOriginalActions.scale (fun t => q (some t))=2*a+4*T
    rw [h.1,h.2]

theorem support_eq (a T : ℕ) (q : profilesAtParameters a T) : support q.1=2*a+4*T :=
  (BinaryCarrierSmallSupportPhysical.mem_profilesAtSupport _ _).mp
    (Finset.mem_filter.mp q.2).1

abbrev ProfileIndex (R a T : ℕ) := (criticalProfiles R) × (profilesAtParameters a T)

def profileMultiplicity (R a T : ℕ) (i : ProfileIndex R a T) :
    CriticalActionKind ⊕ Target → ℕ :=
  BinaryCarrierMixedProfile.multiplicity i.1.1 i.2.1

def profilePredicate (R a T : ℕ) (i : ProfileIndex R a T) :=
  OrbitProfileFull (m := profileMultiplicity R a T i)
    (BinaryCarrierMixedProfile.action points action) 1

/-- Actual original physical subgroups admitting a profile in this bin. -/
abbrev PhysicalFamily (R a T : ℕ) (X : Type*) :=
  AssembledOrbitProfilesOn (profileMultiplicity R a T) (profilePredicate R a T) X

theorem physicalDegree (R a T : ℕ) (i : ProfileIndex R a T) :
    ∑ t, profileMultiplicity R a T i t *
      Fintype.card (BinaryCarrierMixedProfile.points points t) = 2*(R+2*a+4*T) := by
  let j : BinaryCarrierSmallSupportPhysical.ProfileIndex R (2*a+4*T) :=
    ⟨i.1, ⟨i.2.1, (BinaryCarrierSmallSupportPhysical.mem_profilesAtSupport _ _).mpr
      (support_eq a T i.2)⟩⟩
  simpa only [Nat.add_assoc] using BinaryCarrierSmallSupportPhysical.physicalDegree R (2*a+4*T) j

def weightedSum (R a T : ℕ) : ℝ :=
  ∑ p : criticalProfiles R, ∑ q ∈ profilesAtParameters a T,
    modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q

/-- No profile uniqueness is required for the physical upper sum. -/
theorem card_le_factorial_sum (R a T : ℕ) :
    (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) : ℝ) ≤
      ((2*(R+2*a+4*T)).factorial : ℝ) * weightedSum R a T := by
  have h := assembledOrbitProfilesOn_fin_card_le_real
    (profileMultiplicity R a T) (BinaryCarrierMixedProfile.action points action)
    (profilePredicate R a T) (2*(R+2*a+4*T)) (physicalDegree R a T)
    (fun i => orbitProfileFull_family_natural (profileMultiplicity R a T i)
      (BinaryCarrierMixedProfile.action points action))
  apply h.trans_eq
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  simpa only [profileMultiplicity, profilePredicate, modelCount,
    BinaryCarrierMixedProfile.ModelFamily, and_true,
    BinaryCarrierMixedProfile.originalDenominator] using
      (Finset.sum_coe_sort (profilesAtParameters a T) (fun q =>
        modelCount p.1 q / BinaryCarrierMixedProfile.originalDenominator points action p.1 q))

private theorem benchmark_even (n : ℕ) :
    exactBenchmark (2*n) = ((2*n).factorial : ℝ) *
      (binaryGaussianSum n : ℝ) * (criticalCoefficient n : ℝ) := by
  simp [exactBenchmark, halfDegree, parityCoefficient, parity]

/-- The exact original factorial cancels at the complete physical degree. -/
theorem card_div_benchmark_le_weightedSum (R a T : ℕ) :
    (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) : ℝ) /
      exactBenchmark (2*(R+2*a+4*T)) ≤ weightedSum R a T /
        ((criticalCoefficient (R+2*a+4*T) : ℝ) * (binaryGaussianSum (R+2*a+4*T) : ℝ)) := by
  have hf : (0 : ℝ) < ((2*(R+2*a+4*T)).factorial : ℝ) := by positivity
  have hc : (0 : ℝ) < criticalCoefficient (R+2*a+4*T) := by
    exact_mod_cast criticalCoefficient_pos (R+2*a+4*T)
  have hg : (0 : ℝ) < binaryGaussianSum (R+2*a+4*T) := by
    exact_mod_cast binaryGaussianSum_pos (R+2*a+4*T)
  calc
    _ ≤ (((2*(R+2*a+4*T)).factorial : ℝ) * weightedSum R a T) /
        exactBenchmark (2*(R+2*a+4*T)) :=
      div_le_div_of_nonneg_right (card_le_factorial_sum R a T) (exactBenchmark_pos _).le
    _ = _ := by
      rw [benchmark_even]
      field_simp [hf.ne', hc.ne', hg.ne']
      <;> ring

end SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
