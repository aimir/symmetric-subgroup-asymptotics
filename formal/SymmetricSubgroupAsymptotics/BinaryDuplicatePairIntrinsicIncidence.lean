import SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicIncidence
import SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfileUnion
import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureRelabel

/-!
# Intrinsic duplicate-pair incidence

The physical one-quarter duplicate incidence is installed on the complete
noncritical binary family.  Its target has two fewer points and retains the
same occupied noncritical residual orbit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryDuplicatePairIntrinsicIncidence

open BinaryFourPairHallIncidence BinaryFourPairIntrinsicTarget
  BinaryFourPairIntrinsicCoverage

theorem sum_card_eq_sigma {α : Type*} [Fintype α]
    (β : α → Type*) [∀ a, Finite (β a)] :
    (∑ a : α, (Nat.card (β a) : ℚ)) = (Nat.card (Σ a, β a) : ℚ) := by
  rw [Nat.card_sigma,Nat.cast_sum]

abbrev ExteriorIndex (N : ℕ) :=
  BinaryPairE8Profile.ExteriorIndex
    (α := BinaryResidualOrbitMenu.Label (2*N))

abbrev ExteriorPoints (N : ℕ) :=
  BinaryPairE8Profile.exteriorPoints (BinaryResidualOrbitMenu.points (2*N))

abbrev ExteriorAction (N : ℕ) :=
  BinaryPairE8Profile.exteriorAction
    (BinaryResidualOrbitMenu.points (2*N))
    (BinaryResidualOrbitMenu.action (2*N))

abbrev Profile (N : ℕ) :=
  BinaryDuplicatePairProfileUnion.Profile (α := ExteriorIndex N)

def HasNoncriticalResidual (N : ℕ) (t : Profile N) : Prop :=
  ∃ a : BinaryResidualOrbitMenu.Label (2*N),
    IsNoncriticalResidual N a ∧ 0 < t.2 (.inr a)

/-- An actual duplicate mark forces at least two C2 occurrences in every
complete-menu presentation. -/
theorem pair_multiplicity_ge_two (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (C : OrbitProfileFromOrbits.Data H.val (Action N))
    (s : PermutationPairOrbitMarks.DuplicateMark H.val) :
    2 ≤ C.multiplicity (pairIndex N) := by
  let K := relabelSubgroup C.chart.symm H.val
  have hKOn : OrbitProfileFullOn (Action N) (Equiv.refl _) K := by
    simpa only [Equiv.self_trans_symm] using C.chart_full.relabel C.chart.symm
  have hK : OrbitProfileFull (Action N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  have hpairK : Nat.card (PermutationPairOrbitMarks.PairOrbit K) =
      C.multiplicity (pairIndex N) :=
    OrbitProfilePairMarks.pairOrbit_card hK (fullAction_transitive N)
      (pairIndex N) (point_card_two_iff N)
  have htransport : Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) =
      Nat.card (PermutationPairOrbitMarks.PairOrbit K) :=
    Nat.card_congr (PermutationPairOrbitMarks.pairOrbitEquiv C.chart.symm H.val)
  have htwo : 2 ≤ Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) := by
    calc
      2 = s.val.card := s.property.1.symm
      _ ≤ Fintype.card (PermutationPairOrbitMarks.PairOrbit H.val) :=
        Finset.card_le_univ s.val
      _ = Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) :=
        Nat.card_eq_fintype_card.symm
  omega

/-- Every intrinsically noncritical subgroup carrying a duplicate mark has
one exact source profile for the one-quarter incidence. -/
theorem exists_source_profile (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (s : PermutationPairOrbitMarks.DuplicateMark H.val) :
    ∃ t : Profile N,
      2*(t.1+1) +
          RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 =
        2*(N-1) ∧
      HasNoncriticalResidual N t ∧
      ∃ e : OrbitProfilePoints (Points N)
          (BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2 t) ≃ Fin (2*N),
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
  have hpair : 2 ≤ C.multiplicity (pairIndex N) :=
    pair_multiplicity_ge_two N H C s
  let t : Profile N :=
    (C.multiplicity (pairIndex N) - 2,
      fun i => C.multiplicity (.inr i))
  have hm : BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2 t =
      C.multiplicity := by
    funext i
    cases i with
    | inl i =>
      cases i
      change (C.multiplicity (pairIndex N) - 2) + 2 =
        C.multiplicity (pairIndex N)
      omega
    | inr i => rfl
  have hdegree :
      (∑ i, C.multiplicity i * Fintype.card (Points N i)) = 2*N := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr C.chart
  have hdegree' :
      (∑ i, BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2 t i *
        Fintype.card (Points N i)) = 2*N := by
    rw [hm]
    exact hdegree
  have hsize : 2*(t.1+1) +
      RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 =
        2*(N-1) := by
    change (∑ i, RepeatedMarkerMergedProfile.multiplicity t.2 (t.1+2) i *
      Fintype.card (RepeatedMarkerMergedProfile.points (ExteriorPoints N) i)) =
        2*N at hdegree'
    rw [RepeatedMarkerMergedProfile.degree] at hdegree'
    omega
  refine ⟨t,hsize,?_,?_⟩
  · exact ⟨a,hna,hpos⟩
  · rw [hm]
    exact ⟨C.chart,C.chart_full⟩

abbrev MarkedFamily (N : ℕ) :=
  Σ H : NoncriticalBinarySubgroups N,
    PermutationPairOrbitMarks.DuplicateMark H.val

def selectedProfile (N : ℕ) (z : MarkedFamily N) : Profile N :=
  Classical.choose (exists_source_profile N z.1 z.2)

theorem selectedProfile_size (N : ℕ) (z : MarkedFamily N) :
    2*((selectedProfile N z).1+1) +
        RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N)
          (selectedProfile N z).2 = 2*(N-1) :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).1

theorem selectedProfile_noncritical (N : ℕ) (z : MarkedFamily N) :
    HasNoncriticalResidual N (selectedProfile N z) :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).2.1

theorem selectedProfile_full (N : ℕ) (z : MarkedFamily N) :
    ∃ e : OrbitProfilePoints (Points N)
        (BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2
          (selectedProfile N z)) ≃ Fin (2*N),
      OrbitProfileFullOn (Action N) e z.1.val :=
  (Classical.choose_spec (exists_source_profile N z.1 z.2)).2.2

def selector (N : ℕ) : Finset (Profile N) :=
  Finset.univ.image (selectedProfile N)

theorem selector_size (N : ℕ) (t : Profile N) (ht : t ∈ selector N) :
    2*(t.1+1) + RepeatedMarkerMergedProfile.exteriorDegree (ExteriorPoints N) t.2 =
      2*(N-1) := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_size N z

theorem selector_noncritical (N : ℕ) (t : Profile N) (ht : t ∈ selector N) :
    HasNoncriticalResidual N t := by
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp ht
  exact selectedProfile_noncritical N z

abbrev SourceFamily (N : ℕ) :=
  BinaryDuplicatePairProfileUnion.SelectedFamily
    (ExteriorPoints N) (ExteriorAction N) 2 (2*N) (selector N)

abbrev TargetFamily (N : ℕ) :=
  BinaryDuplicatePairProfileUnion.SelectedFamily
    (ExteriorPoints N) (ExteriorAction N) 1 (2*(N-1)) (selector N)

def sourceOfMarked (N : ℕ) (z : MarkedFamily N) : SourceFamily N := by
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

@[simp] theorem sourceOfMarked_val (N : ℕ) (z : MarkedFamily N) :
    (sourceOfMarked N z).val = z.1.val := rfl

def sourceDuplicate (N : ℕ) (z : MarkedFamily N) :
    PermutationPairOrbitMarks.DuplicateMark (sourceOfMarked N z).val := by
  rw [sourceOfMarked_val]
  exact z.2

def sourceMarkedEmbedding (N : ℕ) :
    MarkedFamily N ↪
      (Σ H : SourceFamily N, PermutationPairOrbitMarks.DuplicateMark H.val) where
  toFun z := ⟨sourceOfMarked N z,sourceDuplicate N z⟩
  inj' := by
    rintro ⟨H,s⟩ ⟨K,t⟩ h
    have hp := Sigma.mk.inj_iff.mp h
    have hHK : H = K := by
      apply Subtype.ext
      calc
        H.val = (sourceOfMarked N ⟨H,s⟩).val := (sourceOfMarked_val N ⟨H,s⟩).symm
        _ = (sourceOfMarked N ⟨K,t⟩).val := congrArg Subtype.val hp.1
        _ = K.val := sourceOfMarked_val N ⟨K,t⟩
    exact Sigma.ext hHK (by
      simpa only [sourceDuplicate,sourceOfMarked_val] using hp.2)

local instance sourceFinite (N : ℕ) : Finite (SourceFamily N) :=
  Finite.of_injective
    (fun H : SourceFamily N => (H.val : Set (Equiv.Perm (Fin (2*N)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

theorem intrinsic_duplicate_sum_le_source (N : ℕ) :
    ∑ H : NoncriticalBinarySubgroups N,
        Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) ≤
      ∑ H : SourceFamily N,
        Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) := by
  have h := Nat.card_le_card_of_injective (sourceMarkedEmbedding N)
    (sourceMarkedEmbedding N).injective
  simpa only [Nat.card_sigma] using h

theorem fullOn_isFixedPointFreeBinary (N M : ℕ) {m : FullIndex N → ℕ}
    {e : OrbitProfilePoints (Points N) m ≃ Fin (2*M)}
    {H : Subgroup (Equiv.Perm (Fin (2*M)))}
    (hH : OrbitProfileFullOn (Action N) e H) : IsFixedPointFreeBinary H := by
  constructor
  · let K := relabelSubgroup e.symm H
    have hKOn : OrbitProfileFullOn (Action N) (Equiv.refl _) K := by
      simpa only [Equiv.self_trans_symm] using hH.relabel e.symm
    have hK : OrbitProfileFull (Action N) 1 K :=
      (orbitProfileFullOn_iff _ _ _).mp hKOn
    have hpK : IsPGroup 2 K := BinaryFourPairIntrinsicTarget.fullProfile_isPGroup
      (fun i => fullAction_isPGroup N i) hK
    have hp := hpK.map e.permCongrHom.toMonoidHom
    change IsPGroup 2 (relabelSubgroup e K) at hp
    have heq : relabelSubgroup e K = H := by
      dsimp only [K]
      exact relabelSubgroup_symm e.symm H
    rwa [heq] at hp
  · exact hH.hasNoFixedPoints (fullAction_moves_point N)

theorem fullOn_not_evenCritical (N M : ℕ) {m : FullIndex N → ℕ}
    (a : BinaryResidualOrbitMenu.Label (2*N))
    (ha : IsNoncriticalResidual N a) (hpos : 0 < m (.inr (.inr a)))
    {e : OrbitProfilePoints (Points N) m ≃ Fin (2*M)}
    {H : Subgroup (Equiv.Perm (Fin (2*M)))}
    (hH : OrbitProfileFullOn (Action N) e H) :
    ¬ IsEvenCriticalSubgroup M H := by
  let j : Fin (m (.inr (.inr a))) := ⟨0,hpos⟩
  let x : BinaryResidualOrbitMenu.points (2*N) a := Classical.choice inferInstance
  obtain ⟨o,c,hc⟩ := hH.selected_orbit_image (fullAction_transitive N)
    (.inr (.inr a)) j x
  intro hcritical
  obtain ⟨i,d,hd⟩ :=
    (CriticalOrbitCriterion.isEvenCritical_iff M H).mp hcritical o
  apply ha
  refine ⟨i,d.trans c.symm,?_⟩
  calc
    relabelSubgroup (d.trans c.symm) (criticalActionSubgroup i) =
        relabelSubgroup c.symm (relabelSubgroup d (criticalActionSubgroup i)) :=
      (relabelSubgroup_trans d c.symm _).symm
    _ = relabelSubgroup c.symm (OrbitProfileFromOrbits.orbitImage H o) := by rw [hd]
    _ = BinaryResidualOrbitMenu.action (2*N) a := by
      rw [← hc]
      exact relabelSubgroup_symm c _

theorem targetSelected_isNoncritical (N : ℕ) (H : TargetFamily N) :
    IsFixedPointFreeBinary H.val ∧ ¬ IsEvenCriticalSubgroup (N-1) H.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn (Action N) (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn (Action N) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  obtain ⟨a,ha,hpos⟩ := selector_noncritical N t.val t.property
  exact ⟨fullOn_isFixedPointFreeBinary N (N-1) hOn,
    fullOn_not_evenCritical N (N-1) a ha hpos hOn⟩

def targetEmbedding (N : ℕ) : TargetFamily N ↪ NoncriticalBinarySubgroups (N-1) where
  toFun H := ⟨H.val,targetSelected_isNoncritical N H⟩
  inj' := by
    intro H K h
    exact Subtype.ext
      (congrArg (fun L : NoncriticalBinarySubgroups (N-1) => L.val) h)

local instance targetFinite (N : ℕ) : Finite (TargetFamily N) :=
  Finite.of_injective
    (fun H : TargetFamily N =>
      (H.val : Set (Equiv.Perm (Fin (2*(N-1))))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

def targetPairEmbedding (N : ℕ) :
    (Σ H : TargetFamily N, PermutationPairOrbitMarks.PairOrbit H.val) ↪
      (Σ H : NoncriticalBinarySubgroups (N-1),
        PermutationPairOrbitMarks.PairOrbit H.val) where
  toFun z := ⟨targetEmbedding N z.1,z.2⟩
  inj' := by
    rintro ⟨H,s⟩ ⟨K,t⟩ h
    have hp := Sigma.mk.inj_iff.mp h
    have hHK : H = K := (targetEmbedding N).injective hp.1
    exact Sigma.ext hHK hp.2

theorem target_pair_sum_le_intrinsic (N : ℕ) :
    ∑ H : TargetFamily N, Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) ≤
      ∑ H : NoncriticalBinarySubgroups (N-1),
        Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) := by
  have h := Nat.card_le_card_of_injective (targetPairEmbedding N)
    (targetPairEmbedding N).injective
  simpa only [Nat.card_sigma] using h

theorem selected_normalized_incidence (N : ℕ) (hN : 1 ≤ N) :
    (∑ H : SourceFamily N,
        (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) /
          (2*N).factorial =
      (1/4 : ℚ) *
        ((∑ H : TargetFamily N,
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) /
            (2*(N-1)).factorial) := by
  letI : Fintype (BinaryDuplicatePairProfileUnion.SelectedFamily
      (ExteriorPoints N) (ExteriorAction N) 2 (2*(N-1)+2) (selector N)) :=
    BinaryDuplicatePairProfileUnion.selectedFamilyFintype
      (ExteriorPoints N) (ExteriorAction N) 2 (2*(N-1)+2) (selector N)
  letI : Fintype (TargetFamily N) :=
    BinaryDuplicatePairProfileUnion.selectedFamilyFintype
      (ExteriorPoints N) (ExteriorAction N) 1 (2*(N-1)) (selector N)
  have h := BinaryDuplicatePairProfileUnion.normalized_selected_incidence
    (ExteriorPoints N) (ExteriorAction N) (2*(N-1)) (selector N)
    (selector_size N)
    (BinaryFourPairProfileIncidence.ext_transitive
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.action (2*N))
      (BinaryResidualOrbitMenu.action_transitive (2*N)))
    (BinaryResidualOrbitMenu.e8_residual_separated (2*N))
    (BinaryFourPairProfileIncidence.ext_degree_ne_two
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.point_card_ne_two (2*N)))
  have heq : 2*(N-1)+2 = 2*N := by omega
  let es : BinaryDuplicatePairProfileUnion.SelectedFamily
      (ExteriorPoints N) (ExteriorAction N) 2 (2*(N-1)+2) (selector N) ≃
      SourceFamily N :=
    assembledOrbitProfilesRelabelEquiv
      (fun t : (selector N : Set (Profile N)) =>
        BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2 t.val)
      (fun t => OrbitProfileFull (Action N)
        (m := BinaryDuplicatePairProfileUnion.shiftedMultiplicity 2 t.val) 1)
      (finCongr heq)
  have hs :
      (∑ H : SourceFamily N,
          (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) =
        ∑ H : BinaryDuplicatePairProfileUnion.SelectedFamily
          (ExteriorPoints N) (ExteriorAction N) 2 (2*(N-1)+2) (selector N),
          (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ) := by
    apply (Fintype.sum_equiv es _ _ ?_).symm
    intro H
    simpa only [es,assembledOrbitProfilesRelabelEquiv_val,
      PermutationPairOrbitMarks.duplicateMark_card_relabel]
  have ht :
      (∑ H : TargetFamily N,
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) =
        ∑ H : BinaryDuplicatePairProfileUnion.SelectedFamily
          (ExteriorPoints N) (ExteriorAction N) 1 (2*(N-1)) (selector N),
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ) := by
    rw [sum_card_eq_sigma]
  have hfac : ((2*N).factorial : ℚ) = ((2*(N-1)+2).factorial : ℚ) := by
    rw [heq]
  rw [hs,ht]
  rw [hfac]
  exact h

/-- Complete one-quarter duplicate recurrence for the intrinsic noncritical
family.  The target point-pair is retained on the literal lower-degree
subgroup. -/
theorem intrinsic_normalized_duplicate_incidence (N : ℕ) (hN : 1 ≤ N) :
    (∑ H : NoncriticalBinarySubgroups N,
        (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) /
          (2*N).factorial ≤
      (1/4 : ℚ) *
        ((∑ H : NoncriticalBinarySubgroups (N-1),
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) /
            (2*(N-1)).factorial) := by
  have hsourceNat := intrinsic_duplicate_sum_le_source N
  have hsource :
      (∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) ≤
        ∑ H : SourceFamily N,
          (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ) := by
    exact_mod_cast hsourceNat
  have htargetNat := target_pair_sum_le_intrinsic N
  have htarget :
      (∑ H : TargetFamily N,
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) ≤
        ∑ H : NoncriticalBinarySubgroups (N-1),
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ) := by
    exact_mod_cast htargetNat
  calc
    (∑ H : NoncriticalBinarySubgroups N,
        (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) /
          (2*N).factorial ≤
        (∑ H : SourceFamily N,
          (Nat.card (PermutationPairOrbitMarks.DuplicateMark H.val) : ℚ)) /
            (2*N).factorial :=
      div_le_div_of_nonneg_right hsource (by positivity)
    _ = (1/4 : ℚ) *
        ((∑ H : TargetFamily N,
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) /
            (2*(N-1)).factorial) := selected_normalized_incidence N hN
    _ ≤ (1/4 : ℚ) *
        ((∑ H : NoncriticalBinarySubgroups (N-1),
          (Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) : ℚ)) /
            (2*(N-1)).factorial) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right htarget (by positivity)) (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryDuplicatePairIntrinsicIncidence

end
