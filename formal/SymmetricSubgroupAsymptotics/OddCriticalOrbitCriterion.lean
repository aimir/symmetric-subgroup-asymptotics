import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly
import SymmetricSubgroupAsymptotics.OrbitProfileOrbitCriterion
import SymmetricSubgroupAsymptotics.RepeatedMarkerOrbitProfiles
import SymmetricSubgroupAsymptotics.OddCriticalLiteral
import SymmetricSubgroupAsymptotics.CriticalOrbitCriterion

/-!
# A necessary original-orbit criterion for odd criticality

Every subgroup in the complete odd critical family has, on each literal
orbit, one of the six original odd critical actions: the singleton, the
natural `S_3` action, or one of the four binary critical actions.  This is
the forward criterion needed to exclude a retained noncritical residual
orbit from the odd critical family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

open RepeatedMarkerOrbitProfiles

/-- The literal odd action menu on one point identifies only the fixed
colour. -/
theorem point_card_eq_one_iff (i : OddCriticalActionKind) :
    Nat.card (oddCriticalActionPoints i) = 1 ↔ i = .fixed := by
  cases i with
  | fixed => simp [oddCriticalActionPoints]
  | marker => simp [oddCriticalActionPoints]
  | binary i =>
      cases i <;>
        simp [oddCriticalActionPoints,criticalAction_point_card,criticalActionDegree]

/-- The literal odd action menu on three points identifies only the
natural `S3` colour. -/
theorem point_card_eq_three_iff (i : OddCriticalActionKind) :
    Nat.card (oddCriticalActionPoints i) = 3 ↔ i = .marker := by
  cases i with
  | fixed => simp [oddCriticalActionPoints]
  | marker => simp [oddCriticalActionPoints]
  | binary i =>
      cases i <;>
        simp [oddCriticalActionPoints,criticalAction_point_card,criticalActionDegree]

def AllOddCriticalOrbits {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ o : OrbitProfileFromOrbits.Orbit H,
    ∃ i : OddCriticalActionKind,
      ∃ e : oddCriticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (oddCriticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H o

theorem data_multiplicity_fixed {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X))
    (C : OrbitProfileFromOrbits.Data H oddCriticalActionSubgroup) :
    C.multiplicity .fixed = orbitCount H 1 := by
  change Fintype.card (C.Fiber .fixed) = _
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro o
  change C.label o = .fixed ↔ Nat.card o.orbit = 1
  rw [← Nat.card_congr (C.pointEquiv o)]
  exact (point_card_eq_one_iff (C.label o)).symm

theorem data_multiplicity_marker {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X))
    (C : OrbitProfileFromOrbits.Data H oddCriticalActionSubgroup) :
    C.multiplicity .marker = orbitCount H 3 := by
  change Fintype.card (C.Fiber .marker) = _
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro o
  change C.label o = .marker ↔ Nat.card o.orbit = 3
  rw [← Nat.card_congr (C.pointEquiv o)]
  exact (point_card_eq_three_iff (C.label o)).symm

/-- The converse to the original-orbit test.  The count hypothesis retains
the exact permitted odd shape, so arbitrary collections of singleton or
three-point orbits are not admitted. -/
theorem isCriticalSubgroup_of_orbit_images (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+1))))
    (horbits : AllOddCriticalOrbits H)
    (hshape :
      (orbitCount H 1 = 1 ∧ orbitCount H 3 = 0) ∨
      (orbitCount H 1 = 0 ∧ orbitCount H 3 = 1)) :
    IsCriticalSubgroup (2*N+1) H := by
  choose label pointEquiv image_eq using horbits
  let C : OrbitProfileFromOrbits.Data H oddCriticalActionSubgroup :=
    ⟨label,pointEquiv,image_eq⟩
  let p : CriticalProfile := CriticalOrbitCriterion.profileOfMultiplicity
    (fun i => C.multiplicity (.binary i))
  have hbinary (i : CriticalActionKind) : p.multiplicity i = C.multiplicity (.binary i) := by
    exact congrFun (CriticalOrbitCriterion.profileOfMultiplicity_multiplicity
      (fun i => C.multiplicity (.binary i))) i
  have hdegree :
      (∑ i, C.multiplicity i * Fintype.card (oddCriticalActionPoints i)) = 2*N+1 := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr C.chart
  rcases hshape with hfixed | hmarker
  · have hm : oddCriticalMultiplicity false p = C.multiplicity := by
      funext i
      cases i with
      | fixed =>
          simp [oddCriticalMultiplicity]
          rw [data_multiplicity_fixed H C,hfixed.1]
      | marker =>
          simp [oddCriticalMultiplicity]
          rw [data_multiplicity_marker H C,hfixed.2]
      | binary i => exact hbinary i
    have hrank : p.rank = N := by
      have hd := oddCriticalMultiplicity_degree false p
      rw [hm,hdegree] at hd
      simp at hd
      omega
    let t : OddCriticalProfileIndex N :=
      .inl ⟨p,(mem_criticalProfiles N p).mpr hrank⟩
    have hmt : oddCriticalIndexMultiplicity N t = C.multiplicity := by
      exact hm
    have hfull : ∃ e : OrbitProfilePoints oddCriticalActionPoints
        (oddCriticalIndexMultiplicity N t) ≃ Fin (2*N+1),
        OrbitProfileFullOn oddCriticalActionSubgroup e H := by
      rw [hmt]
      exact ⟨C.chart,C.chart_full⟩
    obtain ⟨e,he⟩ := hfull
    let K := relabelSubgroup e.symm H
    have hKOn : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) K := by
      simpa only [Equiv.self_trans_symm] using he.relabel e.symm
    have hK : OrbitProfileFull oddCriticalActionSubgroup 1 K :=
      (orbitProfileFullOn_iff _ _ _).mp hKOn
    apply (isCriticalSubgroup_odd_iff N H).mpr
    exact ⟨⟨H,t,e,K,hK,relabelSubgroup_symm e.symm H⟩,rfl⟩
  · have hm : oddCriticalMultiplicity true p = C.multiplicity := by
      funext i
      cases i with
      | fixed =>
          simp [oddCriticalMultiplicity]
          rw [data_multiplicity_fixed H C,hmarker.1]
      | marker =>
          simp [oddCriticalMultiplicity]
          rw [data_multiplicity_marker H C,hmarker.2]
      | binary i => exact hbinary i
    have hrank : p.rank = N-1 := by
      have hd := oddCriticalMultiplicity_degree true p
      rw [hm,hdegree] at hd
      simp at hd
      omega
    have hN : 0 < N := by
      have hd := oddCriticalMultiplicity_degree true p
      rw [hm,hdegree] at hd
      simp at hd
      omega
    let t : OddCriticalProfileIndex N :=
      .inr ⟨⟨p,(mem_criticalProfiles (N-1) p).mpr hrank⟩,hN⟩
    have hmt : oddCriticalIndexMultiplicity N t = C.multiplicity := by
      exact hm
    have hfull : ∃ e : OrbitProfilePoints oddCriticalActionPoints
        (oddCriticalIndexMultiplicity N t) ≃ Fin (2*N+1),
        OrbitProfileFullOn oddCriticalActionSubgroup e H := by
      rw [hmt]
      exact ⟨C.chart,C.chart_full⟩
    obtain ⟨e,he⟩ := hfull
    let K := relabelSubgroup e.symm H
    have hKOn : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) K := by
      simpa only [Equiv.self_trans_symm] using he.relabel e.symm
    have hK : OrbitProfileFull oddCriticalActionSubgroup 1 K :=
      (orbitProfileFullOn_iff _ _ _).mp hKOn
    apply (isCriticalSubgroup_odd_iff N H).mpr
    exact ⟨⟨H,t,e,K,hK,relabelSubgroup_symm e.symm H⟩,rfl⟩

theorem orbit_image {N : ℕ} (H : OddCriticalSubgroups N)
    (o : OrbitProfileFromOrbits.Orbit H.val) :
    ∃ i : OddCriticalActionKind,
      ∃ e : oddCriticalActionPoints i ≃ o.orbit,
        relabelSubgroup e (oddCriticalActionSubgroup i) =
          OrbitProfileFromOrbits.orbitImage H.val o := by
  obtain ⟨p,e,L,hL,hLK⟩ := H.property
  have h0 : OrbitProfileFullOn oddCriticalActionSubgroup (Equiv.refl _) L :=
    (orbitProfileFullOn_iff _ _ _).mpr hL
  have hOn : OrbitProfileFullOn oddCriticalActionSubgroup e H.val := by
    rw [← hLK]
    simpa only [Equiv.refl_trans] using h0.relabel e
  obtain ⟨i,j,c,hc⟩ := hOn.orbit_image_chart oddCriticalAction_transitive o
  exact ⟨i,c,hc⟩

theorem all_orbit_images {N : ℕ} (H : OddCriticalSubgroups N) :
    AllOddCriticalOrbits H.val := fun o => orbit_image H o

end SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

end
