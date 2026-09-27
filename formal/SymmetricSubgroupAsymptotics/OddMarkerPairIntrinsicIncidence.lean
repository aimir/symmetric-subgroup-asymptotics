import SymmetricSubgroupAsymptotics.OddMarkerPairProfileUnion
import SymmetricSubgroupAsymptotics.BinaryDuplicatePairIntrinsicIncidence
import SymmetricSubgroupAsymptotics.BinaryPairMomentNormalized
import SymmetricSubgroupAsymptotics.MarkerZeroDefect

/-!
# Intrinsic natural-marker incidence

Every pointed intrinsic noncritical binary subgroup determines its unique
complete orbit profile after the pointed pair occurrence is removed.  A
noncritical residual orbit is retained.  Summing the reversible physical
one-third identity over exactly these profiles identifies the natural `S_3`
zero-defect branch with one third of the intrinsic pair-orbit moment.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.OddMarkerPairIntrinsicIncidence

open BinaryFourPairHallIncidence BinaryFourPairIntrinsicTarget
  BinaryFourPairIntrinsicCoverage
open PermutationPairOrbitMarks

abbrev ExteriorIndex (N : ℕ) :=
  BinaryDuplicatePairIntrinsicIncidence.ExteriorIndex N

abbrev ExteriorPoints (N : ℕ) :=
  BinaryDuplicatePairIntrinsicIncidence.ExteriorPoints N

abbrev ExteriorAction (N : ℕ) :=
  BinaryDuplicatePairIntrinsicIncidence.ExteriorAction N

abbrev Profile (N : ℕ) :=
  BinaryDuplicatePairIntrinsicIncidence.Profile N

abbrev HasNoncriticalResidual (N : ℕ) :=
  BinaryDuplicatePairIntrinsicIncidence.HasNoncriticalResidual N

theorem pair_multiplicity_pos (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (C : OrbitProfileFromOrbits.Data H.val (Action N))
    (s : PairOrbit H.val) :
    0 < C.multiplicity (pairIndex N) := by
  let K := relabelSubgroup C.chart.symm H.val
  have hKOn : OrbitProfileFullOn (Action N) (Equiv.refl _) K := by
    simpa only [Equiv.self_trans_symm] using C.chart_full.relabel C.chart.symm
  have hK : OrbitProfileFull (Action N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  have hpairK : Nat.card (PairOrbit K) = C.multiplicity (pairIndex N) :=
    OrbitProfilePairMarks.pairOrbit_card hK (fullAction_transitive N)
      (pairIndex N) (point_card_two_iff N)
  have htransport : Nat.card (PairOrbit H.val) = Nat.card (PairOrbit K) :=
    Nat.card_congr (pairOrbitEquiv C.chart.symm H.val)
  letI : Nonempty (PairOrbit H.val) := ⟨s⟩
  have hs : 0 < Nat.card (PairOrbit H.val) := Nat.card_pos
  omega

/-- Remove the pointed pair occurrence and retain every other complete
orbit coordinate, including an occupied noncritical residual coordinate. -/
theorem exists_target_profile (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (s : PairOrbit H.val) :
    ∃ t : Profile N,
      2*(t.1+1) +
          RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 =
        2*N ∧
      HasNoncriticalResidual N t ∧
      ∃ e : OrbitProfilePoints (Points N)
          (BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t) ≃ Fin (2*N),
        OrbitProfileFullOn (Action N) e H.val := by
  choose label pointEquiv image_eq using fun o => orbit_cover N H o
  let C : OrbitProfileFromOrbits.Data H.val (Action N) :=
    ⟨label,pointEquiv,image_eq⟩
  obtain ⟨o,ho⟩ :=
    (CriticalOrbitCriterion.not_isEvenCritical_iff N H.val).mp H.property.2
  obtain ⟨a,ha,hna⟩ := residual_label_of_noncritical_orbit N H C o ho
  have hpos : 0 < C.multiplicity (.inr (.inr a)) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨o,ha⟩⟩
  have hpair : 0 < C.multiplicity (pairIndex N) :=
    pair_multiplicity_pos N H C s
  let t : Profile N :=
    (C.multiplicity (pairIndex N) - 1,
      fun i => C.multiplicity (.inr i))
  have hm : BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t =
      C.multiplicity := by
    funext i
    cases i with
    | inl i =>
      cases i
      change (C.multiplicity (pairIndex N) - 1) + 1 =
        C.multiplicity (pairIndex N)
      omega
    | inr i => rfl
  have hdegree :
      (∑ i, C.multiplicity i * Fintype.card (Points N i)) = 2*N := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr C.chart
  have hdegree' :
      (∑ i, BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t i *
        Fintype.card (Points N i)) = 2*N := by
    rw [hm]
    exact hdegree
  have hsize : 2*(t.1+1) +
      RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 = 2*N := by
    change (∑ i, RepeatedMarkerMergedProfile.multiplicity t.2 (t.1+1) i *
      Fintype.card (RepeatedMarkerMergedProfile.points (ExteriorPoints N) i)) =
        2*N at hdegree'
    rw [RepeatedMarkerMergedProfile.degree] at hdegree'
    exact hdegree'
  refine ⟨t,hsize,?_,?_⟩
  · exact ⟨a,hna,hpos⟩
  · rw [hm]
    exact ⟨C.chart,C.chart_full⟩

abbrev MarkedFamily (N : ℕ) :=
  Σ H : NoncriticalBinarySubgroups N, PairOrbit H.val

def selectedProfile (N : ℕ) (z : MarkedFamily N) : Profile N :=
  Classical.choose (exists_target_profile N z.1 z.2)

theorem selectedProfile_size (N : ℕ) (z : MarkedFamily N) :
    2*((selectedProfile N z).1+1) +
        RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N)
          (selectedProfile N z).2 = 2*N :=
  (Classical.choose_spec (exists_target_profile N z.1 z.2)).1

theorem selectedProfile_noncritical (N : ℕ) (z : MarkedFamily N) :
    HasNoncriticalResidual N (selectedProfile N z) :=
  (Classical.choose_spec (exists_target_profile N z.1 z.2)).2.1

theorem selectedProfile_full (N : ℕ) (z : MarkedFamily N) :
    ∃ e : OrbitProfilePoints (Points N)
        (BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1
          (selectedProfile N z)) ≃ Fin (2*N),
      OrbitProfileFullOn (Action N) e z.1.val :=
  (Classical.choose_spec (exists_target_profile N z.1 z.2)).2.2

def selector (N : ℕ) : Finset (Profile N) :=
  Finset.univ.image (selectedProfile N)

theorem selector_size (N : ℕ) (t : Profile N) (ht : t ∈ selector N) :
    2*(t.1+1) +
      RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 = 2*N := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_size N z

theorem selector_noncritical (N : ℕ) (t : Profile N) (ht : t ∈ selector N) :
    HasNoncriticalResidual N t := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_noncritical N z

abbrev TargetFamily (N : ℕ) :=
  BinaryDuplicatePairProfileUnion.SelectedFamily
    (ExteriorPoints N) (ExteriorAction N) 1 (2*N) (selector N)

abbrev NaturalMarkerFamily (N : ℕ) :=
  OddMarkerPairProfileUnion.OddSelectedFamily
    (ExteriorPoints N) (ExteriorAction N) (2*N) (selector N)

def targetOfMarked (N : ℕ) (z : MarkedFamily N) : TargetFamily N := by
  let e := Classical.choose (selectedProfile_full N z)
  have hOn := Classical.choose_spec (selectedProfile_full N z)
  let K := relabelSubgroup e.symm z.1.val
  have hKOn : OrbitProfileFullOn (Action N) (Equiv.refl _) K := by
    simpa only [e,Equiv.self_trans_symm] using hOn.relabel e.symm
  have hK : OrbitProfileFull (Action N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  refine ⟨z.1.val,?_⟩
  refine ⟨⟨selectedProfile N z,
      Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩,e,K,hK,?_⟩
  exact relabelSubgroup_symm e.symm z.1.val

@[simp] theorem targetOfMarked_val (N : ℕ) (z : MarkedFamily N) :
    (targetOfMarked N z).val = z.1.val := rfl

def intrinsicToTargetMarked (N : ℕ) :
    MarkedFamily N ↪ (Σ H : TargetFamily N, PairOrbit H.val) where
  toFun z := ⟨targetOfMarked N z,by simpa using z.2⟩
  inj' := by
    rintro ⟨H,s⟩ ⟨K,t⟩ h
    have hp := Sigma.mk.inj_iff.mp h
    have hHK : H = K := by
      apply Subtype.ext
      calc
        H.val = (targetOfMarked N ⟨H,s⟩).val := (targetOfMarked_val N ⟨H,s⟩).symm
        _ = (targetOfMarked N ⟨K,t⟩).val := congrArg Subtype.val hp.1
        _ = K.val := targetOfMarked_val N ⟨K,t⟩
    exact Sigma.ext hHK (by simpa only [targetOfMarked_val] using hp.2)

theorem target_isNoncritical (N : ℕ) (H : TargetFamily N) :
    IsFixedPointFreeBinary H.val ∧ ¬ IsEvenCriticalSubgroup N H.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn (Action N) (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn (Action N) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  obtain ⟨a,ha,hpos⟩ := selector_noncritical N t.val t.property
  exact ⟨BinaryDuplicatePairIntrinsicIncidence.fullOn_isFixedPointFreeBinary N N hOn,
    BinaryDuplicatePairIntrinsicIncidence.fullOn_not_evenCritical N N a ha hpos hOn⟩

def targetEmbedding (N : ℕ) : TargetFamily N ↪ NoncriticalBinarySubgroups N where
  toFun H := ⟨H.val,target_isNoncritical N H⟩
  inj' := by
    intro H K h
    exact Subtype.ext
      (congrArg (fun L : NoncriticalBinarySubgroups N => L.val) h)

def targetToIntrinsicMarked (N : ℕ) :
    (Σ H : TargetFamily N, PairOrbit H.val) ↪ MarkedFamily N where
  toFun z := ⟨targetEmbedding N z.1,z.2⟩
  inj' := by
    rintro ⟨H,s⟩ ⟨K,t⟩ h
    have hp := Sigma.mk.inj_iff.mp h
    have hHK : H = K := (targetEmbedding N).injective hp.1
    exact Sigma.ext hHK hp.2

local instance targetFinite (N : ℕ) : Finite (TargetFamily N) :=
  Finite.of_injective
    (fun H : TargetFamily N => (H.val : Set (Equiv.Perm (Fin (2*N)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

theorem target_pair_sum_eq_intrinsic (N : ℕ) :
    ∑ H : TargetFamily N, Nat.card (PairOrbit H.val) =
      ∑ H : NoncriticalBinarySubgroups N, Nat.card (PairOrbit H.val) := by
  rw [← Nat.card_sigma,← Nat.card_sigma]
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_injective (targetToIntrinsicMarked N)
      (targetToIntrinsicMarked N).injective
  · exact Nat.card_le_card_of_injective (intrinsicToTargetMarked N)
      (intrinsicToTargetMarked N).injective

private theorem exteriorAction_isPGroup (N : ℕ) :
    ∀ i, IsPGroup 2 (ExteriorAction N i) := by
  intro i
  cases i with
  | inl _ => exact criticalAction_isPGroup .e8
  | inr a => exact BinaryResidualOrbitMenu.action_isPGroup (2*N) a

/-- Exact intrinsic physical incidence.  The natural-marker family is on
`Fin (2N+1)` and the first moment is over the literal noncritical binary
subgroups on `Fin (2N)`. -/
theorem normalized_intrinsic_incidence (N : ℕ) :
    (Nat.card (NaturalMarkerFamily N) : ℚ) / (2*N+1).factorial =
      (1/3 : ℚ) *
        ((∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PairOrbit H.val) : ℚ)) / (2*N).factorial) := by
  have h := OddMarkerPairProfileUnion.normalized_selected_incidence
    (ExteriorPoints N) (ExteriorAction N) (2*N) (selector N)
    (selector_size N) (exteriorAction_isPGroup N)
    (BinaryFourPairProfileIncidence.ext_transitive
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.action (2*N))
      (BinaryResidualOrbitMenu.action_transitive (2*N)))
    (BinaryResidualOrbitMenu.e8_residual_separated (2*N))
    (BinaryFourPairProfileIncidence.ext_degree_ne_two
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.point_card_ne_two (2*N)))
  have heq :
      (∑ H : TargetFamily N, (Nat.card (PairOrbit H.val) : ℚ)) =
        ∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PairOrbit H.val) : ℚ) := by
    exact_mod_cast target_pair_sum_eq_intrinsic N
  rw [heq] at h
  exact h

theorem exactBenchmark_odd (N : ℕ) :
    exactBenchmark (2*N+1) = ((2*N+1).factorial : ℝ) *
      (binaryGaussianSum N : ℝ) * (analyticParityCoefficient 1 N : ℝ) := by
  unfold exactBenchmark
  rw [← analyticParityCoefficient_halfDegree (2*N+1)]
  have hh : halfDegree (2*N+1) = N := by unfold halfDegree; omega
  have hp : parity (2*N+1) = 1 := by unfold parity; omega
  rw [hh,hp]

/-- The natural-marker branch is exactly the coefficient `beta_N` times
the intrinsic binary pair-error moment in the approved normalization. -/
theorem normalized_card (N : ℕ) :
    (Nat.card (NaturalMarkerFamily N) : ℝ) / exactBenchmark (2*N+1) =
      MarkerZeroDefect.beta N * BinaryPairMomentNormalized.pairErrorMomentRatio N := by
  have hQ := normalized_intrinsic_incidence N
  have h := congrArg (fun q : ℚ => (q : ℝ)) hQ
  push_cast at h
  rw [exactBenchmark_odd, BinaryPairMomentNormalized.pairErrorMomentRatio,
    exactBenchmark_even]
  unfold MarkerZeroDefect.beta MarkerZeroDefect.alpha
  have hfodd : (((2*N+1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfeven : (((2*N).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hG : (binaryGaussianSum N : ℝ) ≠ 0 := by
    exact_mod_cast (binaryGaussianSum_pos N).ne'
  have hc : (criticalCoefficient N : ℝ) ≠ 0 := by
    exact_mod_cast (criticalCoefficient_pos N).ne'
  have hp : (analyticParityCoefficient 1 N : ℝ) ≠ 0 := by
    exact_mod_cast (analyticParityCoefficient_positive 1 N).ne'
  have h' := h
  field_simp [hfodd,hfeven] at h'
  field_simp [hfodd,hfeven,hG,hc,hp]
  nlinarith [h']

end SymmetricSubgroupAsymptotics.OddMarkerPairIntrinsicIncidence

end
