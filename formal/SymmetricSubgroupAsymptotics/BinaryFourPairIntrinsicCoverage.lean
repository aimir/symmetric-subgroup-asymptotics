import SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicTarget
import SymmetricSubgroupAsymptotics.OrbitProfilePairMarks
import SymmetricSubgroupAsymptotics.SmallOriginalOrbitCharts

/-!
# Exhaustive intrinsic coverage for the four-pair Hall incidence

Every fixed-point-free binary subgroup is assembled from the original C2
and E8 actions and the finite residual menu.  A noncritical subgroup forces
an occupied noncritical residual colour.  An independent four-frame forces
at least four C2 occurrences, which can be peeled off for the Hall source.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicCoverage

open BinaryFourPairHallIncidence BinaryFourPairIntrinsicTarget

theorem orbit_card_ne_one (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (o : OrbitProfileFromOrbits.Orbit H.val) : Nat.card o.orbit ≠ 1 := by
  intro hc
  have hfixed : o.out ∈ MulAction.fixedPoints H.val (Fin (2*N)) := by
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [← Nat.card_eq_fintype_card, ← o.orbit_eq_orbit_out Quotient.out_eq']
    exact hc
  obtain ⟨h,hh⟩ := H.property.1.2 o.out
  exact hh (hfixed h)

/-- The complete original action menu used by the Hall theorem covers every
literal orbit of an intrinsic noncritical binary subgroup. -/
theorem orbit_cover (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (o : OrbitProfileFromOrbits.Orbit H.val) :
    ∃ i : FullIndex N,
      ∃ e : BinaryFourPairProfileUnion.FullPoints
          (BinaryResidualOrbitMenu.points (2*N)) i ≃ o.orbit,
        relabelSubgroup e
          (BinaryFourPairProfileUnion.FullAction
            (BinaryResidualOrbitMenu.points (2*N))
            (BinaryResidualOrbitMenu.action (2*N)) i) =
          OrbitProfileFromOrbits.orbitImage H.val o := by
  have hbinary : IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H.val o) :=
    H.property.1.1.of_surjective
      (MulAction.toPermHom H.val o.orbit).rangeRestrict
      (MulAction.toPermHom H.val o.orbit).rangeRestrict_surjective
  have h1 := orbit_card_ne_one N H o
  by_cases h2 : Nat.card o.orbit = 2
  · obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.pair_chart H.val o h2
    exact ⟨.inl PUnit.unit,e,he⟩
  by_cases h8 : ∃ e : criticalActionPoints .e8 ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H.val o
  · obtain ⟨e,he⟩ := h8
    exact ⟨.inr (.inl PUnit.unit),e,he⟩
  · obtain ⟨a,e,he⟩ := BinaryResidualOrbitMenu.orbit_cover H.val (2*N)
      (by simp) o hbinary h1 h2 h8
    exact ⟨.inr (.inr a),e,he⟩

abbrev Points (N : ℕ) := BinaryFourPairProfileUnion.FullPoints
  (BinaryResidualOrbitMenu.points (2*N))

abbrev Action (N : ℕ) := BinaryFourPairProfileUnion.FullAction
  (BinaryResidualOrbitMenu.points (2*N))
  (BinaryResidualOrbitMenu.action (2*N))

def pairIndex (N : ℕ) : FullIndex N := .inl PUnit.unit

theorem point_card_two_iff (N : ℕ) (i : FullIndex N) :
    Nat.card (Points N i) = 2 ↔ i = pairIndex N := by
  cases i with
  | inl i =>
    cases i
    constructor
    · exact fun _ => rfl
    · intro _
      change Nat.card (criticalActionPoints .c2) = 2
      rw [Nat.card_eq_fintype_card, criticalAction_point_card]
      rfl
  | inr i =>
    cases i with
    | inl i =>
      cases i
      constructor
      · intro h
        change Nat.card (criticalActionPoints .e8) = 2 at h
        rw [Nat.card_eq_fintype_card, criticalAction_point_card] at h
        norm_num [criticalActionDegree] at h
      · intro h
        cases h
    | inr a =>
      constructor
      · intro h
        exfalso
        apply BinaryResidualOrbitMenu.point_card_ne_two (2*N) a
        rwa [← Nat.card_eq_fintype_card]
      · intro h
        cases h

/-- Four independent actual pair-orbit characters force at least four
literal C2 occurrences in any complete-menu profile of the subgroup. -/
theorem pair_multiplicity_ge_four (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (C : OrbitProfileFromOrbits.Data H.val (Action N))
    (v : PermutationPairOrbitCharacters.Frame H.val 4) :
    4 ≤ C.multiplicity (pairIndex N) := by
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
      Nat.card (PermutationPairOrbitMarks.PairOrbit K) := by
    exact Nat.card_congr
      (PermutationPairOrbitMarks.pairOrbitEquiv C.chart.symm H.val)
  have hfour : 4 ≤ Nat.card (PermutationPairOrbitMarks.PairOrbit H.val) := by
    have h := Nat.card_le_card_of_injective v.val
      (PermutationPairOrbitCharacters.frame_injective H.val v)
    simpa using h
  omega

def chartAtLabel (N : ℕ) {H : Subgroup (Equiv.Perm (Fin (2*N)))}
    (C : OrbitProfileFromOrbits.Data H (Action N))
    (o : OrbitProfileFromOrbits.Orbit H) (i : FullIndex N)
    (hi : C.label o = i) : Points N i ≃ o.orbit :=
  (Equiv.cast (congrArg (Points N) hi).symm).trans (C.pointEquiv o)

theorem chartAtLabel_image (N : ℕ) {H : Subgroup (Equiv.Perm (Fin (2*N)))}
    (C : OrbitProfileFromOrbits.Data H (Action N))
    (o : OrbitProfileFromOrbits.Orbit H) (i : FullIndex N)
    (hi : C.label o = i) :
    relabelSubgroup (chartAtLabel N C o i hi) (Action N i) =
      OrbitProfileFromOrbits.orbitImage H o := by
  subst i
  simpa [chartAtLabel] using C.image_eq o

/-- A noncritical actual orbit must receive a residual label, and that
residual original action is itself noncritical. -/
theorem residual_label_of_noncritical_orbit (N : ℕ)
    (H : NoncriticalBinarySubgroups N)
    (C : OrbitProfileFromOrbits.Data H.val (Action N))
    (o : OrbitProfileFromOrbits.Orbit H.val)
    (ho : ¬ ∃ i : CriticalActionKind,
      ∃ e : criticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (criticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H.val o) :
    ∃ a : BinaryResidualOrbitMenu.Label (2*N),
      C.label o = (.inr (.inr a) : FullIndex N) ∧
        IsNoncriticalResidual N a := by
  generalize hi : C.label o = i
  cases i with
  | inl i =>
    cases i
    exfalso
    apply ho
    let e : criticalActionPoints .c2 ≃ o.orbit :=
      chartAtLabel N C o (pairIndex N) hi
    refine ⟨.c2,e,?_⟩
    exact chartAtLabel_image N C o (pairIndex N) hi
  | inr i =>
    cases i with
    | inl i =>
      cases i
      exfalso
      apply ho
      let e : criticalActionPoints .e8 ≃ o.orbit :=
        chartAtLabel N C o (.inr (.inl PUnit.unit)) hi
      refine ⟨.e8,e,?_⟩
      exact chartAtLabel_image N C o (.inr (.inl PUnit.unit)) hi
    | inr a =>
      refine ⟨a,rfl,?_⟩
      intro ha
      obtain ⟨k,d,hd⟩ := ha
      apply ho
      let e : BinaryResidualOrbitMenu.points (2*N) a ≃ o.orbit :=
        chartAtLabel N C o (.inr (.inr a)) hi
      have he : relabelSubgroup e (BinaryResidualOrbitMenu.action (2*N) a) =
          OrbitProfileFromOrbits.orbitImage H.val o := by
        exact chartAtLabel_image N C o (.inr (.inr a)) hi
      refine ⟨k,d.trans e,?_⟩
      calc
        relabelSubgroup (d.trans e) (criticalActionSubgroup k) =
            relabelSubgroup e (relabelSubgroup d (criticalActionSubgroup k)) :=
          (relabelSubgroup_trans d e _).symm
        _ = relabelSubgroup e (BinaryResidualOrbitMenu.action (2*N) a) := by
          rw [hd]
        _ = _ := he

/-- Every intrinsically noncritical subgroup carrying a four-frame has one
exact Hall source profile.  The profile has the correct total degree and an
occupied noncritical residual colour. -/
theorem exists_source_profile (N : ℕ) (H : NoncriticalBinarySubgroups N)
    (v : PermutationPairOrbitCharacters.Frame H.val 4) :
    ∃ t : ResidualProfile N,
      BinaryFourPairProfileUnion.ProfileSize
        (BinaryResidualOrbitMenu.points (2*N)) N t ∧
      HasNoncriticalResidual N t ∧
      ∃ e : OrbitProfilePoints (Points N)
          (BinaryFourPairProfileUnion.sourceMultiplicity t) ≃ Fin (2*N),
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
  have hpair : 4 ≤ C.multiplicity (pairIndex N) :=
    pair_multiplicity_ge_four N H C v
  let t : ResidualProfile N :=
    ((C.multiplicity (pairIndex N) - 4,
      C.multiplicity (.inr (.inl PUnit.unit))),
      fun b => C.multiplicity (.inr (.inr b)))
  have hm : BinaryFourPairProfileUnion.sourceMultiplicity t = C.multiplicity := by
    funext i
    cases i with
    | inl i =>
      cases i
      change (C.multiplicity (pairIndex N) - 4) + 4 =
        C.multiplicity (pairIndex N)
      omega
    | inr i =>
      cases i <;> rfl
  have hdegree :
      (∑ i, C.multiplicity i * Fintype.card (Points N i)) = 2*N := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr C.chart
  have hdegree' :
      (∑ i, BinaryFourPairProfileUnion.sourceMultiplicity t i *
        Fintype.card (Points N i)) = 2*N := by
    rw [hm]
    exact hdegree
  have hsize : BinaryFourPairProfileUnion.ProfileSize
      (BinaryResidualOrbitMenu.points (2*N)) N t := by
    change (∑ i, RepeatedMarkerMergedProfile.multiplicity
      (BinaryPairE8Profile.exteriorMultiplicity t.2 t.1.2) (t.1.1+4) i *
      Fintype.card (RepeatedMarkerMergedProfile.points
        (BinaryPairE8Profile.exteriorPoints
          (BinaryResidualOrbitMenu.points (2*N))) i)) = 2*N at hdegree'
    rw [RepeatedMarkerMergedProfile.degree,
      BinaryFourPairProfileIncidence.exterior_degree] at hdegree'
    dsimp only [BinaryFourPairProfileUnion.ProfileSize]
    omega
  refine ⟨t,hsize,?_,?_⟩
  · exact ⟨a,hna,hpos⟩
  · rw [hm]
    exact ⟨C.chart,C.chart_full⟩

end SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicCoverage

end
