import SymmetricSubgroupAsymptotics.RepeatedMarkerZeroDefect
import SymmetricSubgroupAsymptotics.OddZeroDefectBinaryFamily
import SymmetricSubgroupAsymptotics.OddCriticalOrbitCriterion

/-!
# Exhaustive coverage of the odd zero-defect branch

This file supplies the inverse direction missing from the already counted
two-sector construction.  The singleton sector is recovered by deleting
the unique fixed point.  The natural-marker sector is recovered by the
fusion-natural marker contraction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.OddZeroDefectCoverage

open RepeatedMarkerOrbitProfiles RepeatedMarkerZeroDefect
open BinaryFourPairIntrinsicTarget BinaryFourPairIntrinsicCoverage

abbrev ZeroFamily (N : ℕ) :=
  Family N 1 (fun H => ¬ IsCriticalSubgroup (2*N+1) H)

/-- A single singleton orbit is the same as a unique global fixed point.
The point itself is recovered from the literal orbit quotient. -/
theorem existsUnique_fixedPoint_of_orbitCount_eq_one {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (hcount : orbitCount H 1 = 1) :
    ∃! x : X, ∀ h : H, (h : Equiv.Perm X) x = x := by
  let S := {o : OrbitProfileFromOrbits.Orbit H // Nat.card o.orbit = 1}
  have hcard : Nat.card S = 1 := hcount
  have hsub : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hnonempty : Nonempty S := (Nat.card_eq_one_iff_unique.mp hcard).2
  let q : S := Classical.choice hnonempty
  let x : X := q.1.out
  have hxmem : x ∈ MulAction.fixedPoints H X := by
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [← Nat.card_eq_fintype_card,
      ← q.1.orbit_eq_orbit_out Quotient.out_eq']
    exact q.2
  refine ⟨x,(MulAction.mem_fixedPoints.mp hxmem),?_⟩
  intro y hy
  have hymem : y ∈ MulAction.fixedPoints H X := MulAction.mem_fixedPoints.mpr hy
  let qy : S := ⟨Quotient.mk'' y,by
    rw [MulAction.orbitRel.Quotient.orbit_mk,Nat.card_eq_fintype_card]
    exact MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hymem⟩
  have hqy : qy = q := hsub.elim _ _
  have hyq : y ∈ q.1.orbit := by
    apply MulAction.orbitRel.Quotient.mem_orbit.mpr
    exact congrArg Subtype.val hqy
  apply (MulAction.mem_fixedPoints'.mp hxmem) y
  rw [q.1.orbit_eq_orbit_out Quotient.out_eq'] at hyq
  exact hyq

/-- Extending a subgroup whose every orbit is one of the four critical
binary actions by one fixed point gives the exact singleton-shaped odd
critical orbit menu. -/
theorem singletonExtension_allOddCriticalOrbits {α X : Type}
    [Fintype α] [Fintype X] [DecidableEq α]
    (e : X ≃ Option α) (x : X) (hx : e x = none)
    (K : Subgroup (Equiv.Perm α))
    (hK : CriticalOrbitCriterion.AllCriticalOrbits K) :
    OddCriticalOrbitCriterion.AllOddCriticalOrbits
      (K.map (SingletonExtension.extensionHom e)) := by
  let H := K.map (SingletonExtension.extensionHom e)
  intro O
  by_cases hcard : Nat.card O.orbit = 1
  · obtain ⟨c,hc⟩ := SmallOriginalOrbitCharts.singleton_chart H O hcard
    let u : Fin 1 ≃ PUnit.{1} := Equiv.ofUnique _ _
    refine ⟨.fixed,u.trans c,?_⟩
    change relabelSubgroup (u.trans c) (⊤ : Subgroup (Equiv.Perm (Fin 1))) = _
    rw [← hc]
    calc
      relabelSubgroup (u.trans c) (⊤ : Subgroup (Equiv.Perm (Fin 1))) =
          relabelSubgroup c (relabelSubgroup u ⊤) :=
        (relabelSubgroup_trans u c _).symm
      _ = relabelSubgroup c ⊤ := by rw [(relabelSubgroup u).map_top]
  · have hout_ne : O.out ≠ x := by
      intro hout
      apply hcard
      have hfix : O.out ∈ MulAction.fixedPoints H X := by
        apply MulAction.mem_fixedPoints.mpr
        intro g
        obtain ⟨k,hk,hkg⟩ := Subgroup.mem_map.mp g.property
        change (g : Equiv.Perm X) O.out = O.out
        rw [← hkg,hout]
        exact SingletonExtension.extensionHom_fixes e x hx k
      rw [O.orbit_eq_orbit_out Quotient.out_eq',Nat.card_eq_fintype_card]
      exact MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hfix
    have heout : e O.out ≠ none := by
      intro hnone
      apply hout_ne
      exact e.injective (hnone.trans hx.symm)
    obtain ⟨a,ha⟩ : ∃ a : α, e O.out = some a := by
      cases h : e O.out with
      | none => exact False.elim (heout h)
      | some a => exact ⟨a,rfl⟩
    let o : OrbitProfileFromOrbits.Orbit K := Quotient.mk'' a
    have hEO : SingletonExtension.extendedOrbit e K o = O := by
      apply MulAction.orbitRel.Quotient.mem_orbit.mp
      rw [O.orbit_eq_orbit_out Quotient.out_eq']
      have hout_mem : o.out ∈ MulAction.orbit K a := by
        change o.out ∈ o.orbit
        exact MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)
      obtain ⟨k,hk⟩ := hout_mem
      refine ⟨⟨SingletonExtension.extensionHom e k.1,
        Subgroup.mem_map.mpr ⟨k.1,k.2,rfl⟩⟩,?_⟩
      change SingletonExtension.extensionHom e k.1 O.out = e.symm (some o.out)
      rw [show O.out = e.symm (some a) by
        apply e.injective
        simpa only [Equiv.apply_symm_apply] using ha]
      rw [SingletonExtension.extensionHom_some]
      exact congrArg e.symm (congrArg some hk)
    subst O
    obtain ⟨i,c,hc⟩ := hK o
    let φ := SingletonExtension.orbitEquiv e K o
    refine ⟨.binary i,c.trans φ,?_⟩
    calc
      relabelSubgroup (c.trans φ) (criticalActionSubgroup i) =
          relabelSubgroup φ (relabelSubgroup c (criticalActionSubgroup i)) :=
        (relabelSubgroup_trans c φ _).symm
      _ = relabelSubgroup φ (OrbitProfileFromOrbits.orbitImage K o) := by rw [hc]
      _ = OrbitProfileFromOrbits.orbitImage H
          (SingletonExtension.extendedOrbit e K o) := by
        exact SingletonExtension.relabel_orbitImage e K o

/-- Deleting the unique fixed point from the singleton-shaped zero branch
produces an intrinsic noncritical fixed-point-free binary subgroup, and
extending it back recovers the original subgroup exactly. -/
theorem exists_singleton_source (N : ℕ) (H : ZeroFamily N)
    (hmarker : orbitCount H.1 3 = 0) :
    ∃ x : Fin (2*N+1), ∃ K : NoncriticalBinarySubgroups N,
      K.val.map (SingletonExtension.extensionHom (finSuccEquiv' x)) = H.1 := by
  have hsum := marker_fixed_eq_epsilon N 1 (by omega)
    (fun L => ¬ IsCriticalSubgroup (2*N+1) L) H
  have hfixed : orbitCount H.1 1 = 1 := by omega
  obtain ⟨x,hx,hxunique⟩ :=
    existsUnique_fixedPoint_of_orbitCount_eq_one H.1 hfixed
  let e : Fin (2*N+1) ≃ Option (Fin (2*N)) := finSuccEquiv' x
  let K0 : Subgroup (Equiv.Perm (Fin (2*N))) :=
    H.1.comap (SingletonExtension.extensionHom e)
  have hmap : K0.map (SingletonExtension.extensionHom e) = H.1 := by
    exact SingletonExtension.map_comap_eq_of_fixes e x (finSuccEquiv'_at x) H.1 hx
  have hpH : IsPGroup 2 H.1 :=
    isPGroup_of_marker_count_zero H.1 H.2.1 hmarker
  let φ : K0 →* H.1 :=
    { toFun := fun k => ⟨SingletonExtension.extensionHom e k.1,k.2⟩
      map_one' := Subtype.ext (map_one (SingletonExtension.extensionHom e))
      map_mul' := fun a b =>
        Subtype.ext (map_mul (SingletonExtension.extensionHom e) a.1 b.1) }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply SingletonExtension.extensionHom_injective e
    exact congrArg (fun z : H.1 => z.1) hab
  have hpK : IsPGroup 2 K0 := hpH.of_injective φ hφ
  have hno : HasNoFixedPoints K0 := by
    intro y
    let z : Fin (2*N+1) := e.symm (some y)
    have hzx : z ≠ x := by
      intro h
      have heq := congrArg e h
      dsimp only [z] at heq
      rw [Equiv.apply_symm_apply] at heq
      exact Option.some_ne_none y (heq.trans (finSuccEquiv'_at x))
    have hnot : ¬ ∀ h : H.1, (h : Equiv.Perm (Fin (2*N+1))) z = z := by
      intro hall
      exact hzx (hxunique z hall)
    obtain ⟨h,hh⟩ := not_forall.mp hnot
    have hhmem : h.1 ∈ K0.map (SingletonExtension.extensionHom e) := by
      rw [hmap]
      exact h.2
    obtain ⟨g,hg,hgeq⟩ := Subgroup.mem_map.mp hhmem
    refine ⟨⟨g,hg⟩,?_⟩
    intro hgy
    apply hh
    rw [← hgeq]
    change SingletonExtension.extensionHom e g (e.symm (some y)) = e.symm (some y)
    rw [SingletonExtension.extensionHom_some,hgy]
  have hnoncritical : ¬ IsEvenCriticalSubgroup N K0 := by
    intro hcritical
    apply H.2.2.2
    have hKO : CriticalOrbitCriterion.AllCriticalOrbits K0 :=
      (CriticalOrbitCriterion.isEvenCritical_iff N K0).mp hcritical
    apply OddCriticalOrbitCriterion.isCriticalSubgroup_of_orbit_images N H.1
    · rw [← hmap]
      exact singletonExtension_allOddCriticalOrbits e x (finSuccEquiv'_at x) K0 hKO
    · exact Or.inl ⟨hfixed,hmarker⟩
  exact ⟨x,⟨K0,⟨hpK,hno⟩,hnoncritical⟩,hmap⟩

theorem singleton_mem_sector (N : ℕ) (H : ZeroFamily N)
    (hmarker : orbitCount H.1 3 = 0) :
    H.1 ∈ Set.range (OddZeroDefectBinaryFamily.subgroup N) := by
  obtain ⟨x,K,hK⟩ := exists_singleton_source N H hmarker
  let L : OddZeroDefectBinaryFamily.SingletonSector N := ⟨H.1,x,K,hK⟩
  exact ⟨Sum.inl L,rfl⟩

abbrev MarkerPoints (N : ℕ) :=
  OddMarkerPairModelEquiv.OddPoints
    (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)

abbrev MarkerAction (N : ℕ) :=
  OddMarkerPairModelEquiv.OddAction
    (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
    (OddMarkerPairIntrinsicIncidence.ExteriorAction N)

theorem marker_point_card_three_iff (N : ℕ)
    (i : PUnit.{1} ⊕ FullIndex N) :
    Nat.card (MarkerPoints N i) = 3 ↔ i = .inl PUnit.unit := by
  cases i with
  | inl i =>
      cases i
      show Nat.card (Fin 3) = 3 ↔
        (Sum.inl PUnit.unit : PUnit.{1} ⊕ FullIndex N) = Sum.inl PUnit.unit
      constructor
      · intro _
        rfl
      · intro _
        exact Nat.card_fin 3
  | inr i =>
      have hne : Nat.card (MarkerPoints N (.inr i)) ≠ 3 := by
        rw [Nat.card_eq_fintype_card]
        exact RepeatedOddMarkerPhysicalBinary.exteriorDegree_ne_three
          (OddMarkerPairModelEquiv.BasePoints
            (OddMarkerPairIntrinsicIncidence.ExteriorPoints N))
          (OddMarkerPairModelEquiv.BaseAction
            (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
            (OddMarkerPairIntrinsicIncidence.ExteriorAction N))
          (fullAction_isPGroup N) (fullAction_transitive N) i
      constructor
      · intro h
        exact False.elim (hne h)
      · intro h
        cases h

theorem marker_orbit_cover (N : ℕ) (H : Subgroup (Equiv.Perm (Fin (2*N+1))))
    (hfits : Fits H) (hfixed : orbitCount H 1 = 0)
    (o : OrbitProfileFromOrbits.Orbit H) :
    ∃ i : PUnit.{1} ⊕ FullIndex N, ∃ e : MarkerPoints N i ≃ o.orbit,
      relabelSubgroup e (MarkerAction N i) = OrbitProfileFromOrbits.orbitImage H o := by
  rcases hfits o with hp | ⟨e,he⟩
  · have h1 : Nat.card o.orbit ≠ 1 :=
      orbit_card_ne_of_count_eq_zero H hfixed o
    let z : o.orbit := ⟨o.out,by
      rw [o.orbit_eq_orbit_out Quotient.out_eq']
      exact MulAction.mem_orbit_self o.out⟩
    have htrans : ∀ y : o.orbit,
        ∃ u : OrbitProfileFromOrbits.orbitImage H o, u • z = y := by
      intro y
      have hyq : Quotient.mk'' y.1 = o :=
        MulAction.orbitRel.Quotient.mem_orbit.mp y.2
      have hzq : Quotient.mk'' z.1 = o :=
        MulAction.orbitRel.Quotient.mem_orbit.mp z.2
      have hq : Quotient.mk'' y.1 = Quotient.mk'' z.1 := hyq.trans hzq.symm
      have hyz : y.1 ∈ MulAction.orbit H z.1 :=
        MulAction.orbitRel_apply.mp (Quotient.exact hq)
      obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hyz
      let u : OrbitProfileFromOrbits.orbitImage H o :=
        ⟨MulAction.toPermHom H o.orbit h,⟨h,rfl⟩⟩
      refine ⟨u,Subtype.ext ?_⟩
      exact hh
    obtain ⟨k,hk⟩ := pGroup_transitive_degree hp z htrans
    have hkpos : 0 < k := by
      by_contra hkzero
      have hk0 : k = 0 := by omega
      apply h1
      rw [hk,hk0,pow_zero]
    have heven : 2 ∣ Nat.card o.orbit := by
      rw [hk]
      exact dvd_pow_self 2 (Nat.ne_of_gt hkpos)
    have hambient : Nat.card o.orbit ≤ 2*N+1 := by
      rw [Nat.card_eq_fintype_card]
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective (fun y : o.orbit => (y : Fin (2*N+1)))
          Subtype.val_injective
    have hbound : Nat.card o.orbit ≤ 2*N := by omega
    by_cases h2 : Nat.card o.orbit = 2
    · obtain ⟨e,he⟩ := SmallOriginalOrbitCharts.pair_chart H o h2
      exact ⟨.inr (.inl PUnit.unit),e,he⟩
    by_cases h8 : ∃ e : criticalActionPoints .e8 ≃ o.orbit,
        relabelSubgroup e (criticalActionSubgroup .e8) =
          OrbitProfileFromOrbits.orbitImage H o
    · obtain ⟨e,he⟩ := h8
      exact ⟨.inr (.inr (.inl PUnit.unit)),e,he⟩
    · obtain ⟨a,e,he⟩ := BinaryResidualOrbitMenu.orbit_cover_of_orbit_card_le
        H (2*N) o hp h1 h2 h8 hbound
      exact ⟨.inr (.inr (.inr a)),e,he⟩
  · exact ⟨.inl PUnit.unit,e,he⟩

theorem marker_multiplicity (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+1))))
    (C : OrbitProfileFromOrbits.Data H (MarkerAction N)) :
    C.multiplicity (.inl PUnit.unit) = orbitCount H 3 := by
  change Fintype.card (C.Fiber (.inl PUnit.unit)) = _
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro o
  change C.label o = .inl PUnit.unit ↔ Nat.card o.orbit = 3
  rw [← Nat.card_congr (C.pointEquiv o)]
  exact (marker_point_card_three_iff N (C.label o)).symm

/-- Every natural-marker-shaped zero profile has one complete marker/pair/
E8/residual presentation on its original labelled points. -/
theorem exists_marker_profile (N : ℕ) (H : ZeroFamily N)
    (hfixed : orbitCount H.1 1 = 0) :
    ∃ t : OddMarkerPairIntrinsicIncidence.Profile N,
      2*(t.1+1) + RepeatedMarkerMergedProfile.exteriorDegree
        (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2 = 2*N ∧
      ∃ e : OrbitProfilePoints (MarkerPoints N)
          (OddMarkerPairProfileUnion.oddMultiplicity t) ≃ Fin (2*N+1),
        OrbitProfileFullOn (MarkerAction N) e H.1 := by
  choose label pointEquiv image_eq using fun o =>
    marker_orbit_cover N H.1 H.2.1 hfixed o
  let C : OrbitProfileFromOrbits.Data H.1 (MarkerAction N) :=
    ⟨label,pointEquiv,image_eq⟩
  let t : OddMarkerPairIntrinsicIncidence.Profile N :=
    (C.multiplicity (.inr (.inl PUnit.unit)),
      fun i => C.multiplicity (.inr (.inr i)))
  have hsum := marker_fixed_eq_epsilon N 1 (by omega)
    (fun L => ¬ IsCriticalSubgroup (2*N+1) L) H
  have hmarker : orbitCount H.1 3 = 1 := by omega
  have hm : OddMarkerPairProfileUnion.oddMultiplicity t = C.multiplicity := by
    funext i
    cases i with
    | inl i =>
        cases i
        change 1 = C.multiplicity (.inl PUnit.unit)
        rw [marker_multiplicity N H.1 C,hmarker]
    | inr i =>
        cases i with
        | inl i => cases i; rfl
        | inr i => rfl
  have hdegree :
      (∑ i, C.multiplicity i * Fintype.card (MarkerPoints N i)) = 2*N+1 := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr C.chart
  have hdegree' :
      (∑ i, OddMarkerPairProfileUnion.oddMultiplicity t i *
        Fintype.card (MarkerPoints N i)) = 2*N+1 := by
    rw [hm]
    exact hdegree
  have hsize : 2*(t.1+1) + RepeatedMarkerMergedProfile.exteriorDegree
      (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2 = 2*N := by
    change (∑ i, RepeatedOddMarkerPhysicalProfile.multiplicity
      (RepeatedMarkerMergedProfile.multiplicity t.2 t.1) 1 i *
      Fintype.card (RepeatedOddMarkerPhysicalProfile.points
        (RepeatedMarkerMergedProfile.points
          (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)) i)) = 2*N+1 at hdegree'
    rw [RepeatedOddMarkerPhysicalProfile.physicalDegree,
      RepeatedMarkerMergedProfile.degree] at hdegree'
    omega
  refine ⟨t,hsize,?_⟩
  rw [hm]
  exact ⟨C.chart,C.chart_full⟩

theorem exteriorAction_isPGroup (N : ℕ)
    (i : OddMarkerPairIntrinsicIncidence.ExteriorIndex N) :
    IsPGroup 2 (OddMarkerPairIntrinsicIncidence.ExteriorAction N i) := by
  exact fullAction_isPGroup N (.inr i)

theorem markerAction_transitive (N : ℕ) (i : PUnit.{1} ⊕ FullIndex N)
    (x y : MarkerPoints N i) :
    ∃ u : MarkerAction N i, (u : Equiv.Perm (MarkerPoints N i)) x = y := by
  exact RepeatedOddMarkerPhysicalProfile.action_transitive
    (OddMarkerPairModelEquiv.BasePoints
      (OddMarkerPairIntrinsicIncidence.ExteriorPoints N))
    (OddMarkerPairModelEquiv.BaseAction
      (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
      (OddMarkerPairIntrinsicIncidence.ExteriorAction N))
    (fullAction_transitive N) i x y

theorem fullAction_separated (N : ℕ) :
    OrbitActionTypesSeparated (Points N) (Action N) := by
  exact RepeatedMarkerMergedProfile.action_separated
    (OddMarkerPairIntrinsicIncidence.ExteriorPoints N)
    (OddMarkerPairIntrinsicIncidence.ExteriorAction N)
    (BinaryResidualOrbitMenu.e8_residual_separated (2*N))
    (BinaryFourPairProfileIncidence.ext_degree_ne_two
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.point_card_ne_two (2*N)))

def pairOrbit_of_fullOn (N : ℕ) {m : FullIndex N → ℕ}
    {e : OrbitProfilePoints (Points N) m ≃ Fin (2*N)}
    {B : Subgroup (Equiv.Perm (Fin (2*N)))}
    (hOn : OrbitProfileFullOn (Action N) e B)
    (hpos : 0 < m (pairIndex N)) :
    PermutationPairOrbitMarks.PairOrbit B := by
  let j : Fin (m (pairIndex N)) := ⟨0,hpos⟩
  let x : Points N (pairIndex N) := Classical.choice inferInstance
  let hw := hOn.selected_orbit_image (fullAction_transitive N)
    (pairIndex N) j x
  let o := Classical.choose hw
  let c := Classical.choose (Classical.choose_spec hw)
  have hc := Classical.choose_spec (Classical.choose_spec hw)
  refine ⟨o.orbit,?_,?_⟩
  · exact ⟨o.out,o.orbit_eq_orbit_out Quotient.out_eq'⟩
  · rw [← Nat.card_congr c]
    exact (point_card_two_iff N (pairIndex N)).mpr rfl

theorem selectedProfile_eq_of_fullOn (N : ℕ)
    (B : NoncriticalBinarySubgroups N)
    (s : PermutationPairOrbitMarks.PairOrbit B.val)
    (t : OddMarkerPairIntrinsicIncidence.Profile N)
    {e : OrbitProfilePoints (Points N)
      (BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t) ≃ Fin (2*N)}
    (hOn : OrbitProfileFullOn (Action N) e B.val) :
    OddMarkerPairIntrinsicIncidence.selectedProfile N ⟨B,s⟩ = t := by
  obtain ⟨d,hd⟩ := OddMarkerPairIntrinsicIncidence.selectedProfile_full N ⟨B,s⟩
  have hm := hOn.multiplicity_unique hd (fullAction_transitive N)
    (fullAction_separated N)
  exact (BinaryDuplicatePairProfileUnion.shiftedMultiplicity_injective 1 hm).symm

/-- If the odd subgroup is outside the critical owner, its complete marker
profile retains an occupied exterior action outside the four critical binary
actions. -/
theorem marker_profile_has_noncritical_residual (N : ℕ) (H : ZeroFamily N)
    (hfixed : orbitCount H.1 1 = 0)
    (t : OddMarkerPairIntrinsicIncidence.Profile N)
    {e : OrbitProfilePoints (MarkerPoints N)
      (OddMarkerPairProfileUnion.oddMultiplicity t) ≃ Fin (2*N+1)}
    (hOn : OrbitProfileFullOn (MarkerAction N) e H.1) :
    OddMarkerPairIntrinsicIncidence.HasNoncriticalResidual N t := by
  by_contra hnone
  have hall : OddCriticalOrbitCriterion.AllOddCriticalOrbits H.1 := by
    intro o
    obtain ⟨i,j,c,hc⟩ := hOn.orbit_image_chart
      (markerAction_transitive N) o
    cases i with
    | inl i =>
        cases i
        exact ⟨.marker,c,hc⟩
    | inr i =>
        cases i with
        | inl i =>
            cases i
            exact ⟨.binary .c2,c,hc⟩
        | inr i =>
            cases i with
            | inl i =>
                cases i
                exact ⟨.binary .e8,c,hc⟩
            | inr a =>
                have hj := j.isLt
                change j.val < t.2 (.inr a) at hj
                have hpos : 0 < t.2 (.inr a) := by omega
                have hncritical : ¬ IsNoncriticalResidual N a := by
                  intro ha
                  exact hnone ⟨a,ha,hpos⟩
                obtain ⟨k,d,hd⟩ := Classical.not_not.mp hncritical
                refine ⟨.binary k,d.trans c,?_⟩
                calc
                  relabelSubgroup (d.trans c) (criticalActionSubgroup k) =
                      relabelSubgroup c
                        (relabelSubgroup d (criticalActionSubgroup k)) :=
                    (relabelSubgroup_trans d c _).symm
                  _ = relabelSubgroup c
                        (BinaryResidualOrbitMenu.action (2*N) a) := by rw [hd]
                  _ = OrbitProfileFromOrbits.orbitImage H.1 o := hc
  have hsum := marker_fixed_eq_epsilon N 1 (by omega)
    (fun L => ¬ IsCriticalSubgroup (2*N+1) L) H
  have hmarker : orbitCount H.1 3 = 1 := by omega
  exact H.2.2.2 (OddCriticalOrbitCriterion.isCriticalSubgroup_of_orbit_images
    N H.1 hall (Or.inr ⟨hfixed,hmarker⟩))

/-- Contract the unique natural marker in a complete odd profile to one
additional pair occurrence, retaining the whole exterior profile. -/
theorem contract_marker_profile (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+1))))
    (t : OddMarkerPairIntrinsicIncidence.Profile N)
    (hsize : 2*(t.1+1) + RepeatedMarkerMergedProfile.exteriorDegree
      (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2 = 2*N)
    (e : OrbitProfilePoints (MarkerPoints N)
      (OddMarkerPairProfileUnion.oddMultiplicity t) ≃ Fin (2*N+1))
    (hOn : OrbitProfileFullOn (MarkerAction N) e H) :
    ∃ B : Subgroup (Equiv.Perm (Fin (2*N))),
      OrbitProfileFullOn (Action N)
        (BinaryDuplicatePairProfileUnion.finChart
          (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2 (t.1+1)
          (2*N) hsize) B := by
  let K := relabelSubgroup e.symm H
  have hKOn : OrbitProfileFullOn (MarkerAction N) (Equiv.refl _) K := by
    simpa only [Equiv.self_trans_symm] using hOn.relabel e.symm
  have hK : OrbitProfileFull (MarkerAction N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  let Y : OddMarkerPairModelEquiv.OddModel
      (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2
      (OddMarkerPairIntrinsicIncidence.ExteriorAction N) t.1 := ⟨K,hK⟩
  let L := OddMarkerPairModelEquiv.modelEquiv
    (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2
    (OddMarkerPairIntrinsicIncidence.ExteriorAction N) t.1
    (exteriorAction_isPGroup N) Y
  let d := BinaryDuplicatePairProfileUnion.finChart
    (OddMarkerPairIntrinsicIncidence.ExteriorPoints N) t.2 (t.1+1)
    (2*N) hsize
  let B := relabelSubgroup d L.val
  have hLOn : OrbitProfileFullOn (Action N) (Equiv.refl _) L.val :=
    (orbitProfileFullOn_iff _ _ _).mpr L.property
  refine ⟨B,?_⟩
  simpa only [d,B,Equiv.refl_trans] using hLOn.relabel d

/-- Every marker-shaped odd zero-defect subgroup belongs to the already
counted natural-marker sector. -/
theorem marker_mem_sector (N : ℕ) (H : ZeroFamily N)
    (hfixed : orbitCount H.1 1 = 0) :
    H.1 ∈ Set.range (OddZeroDefectBinaryFamily.subgroup N) := by
  obtain ⟨t,hsize,e,hOn⟩ := exists_marker_profile N H hfixed
  have hres := marker_profile_has_noncritical_residual N H hfixed t hOn
  obtain ⟨B0,hBOn⟩ := contract_marker_profile N H.1 t hsize e hOn
  have hbinary : IsFixedPointFreeBinary B0 :=
    BinaryDuplicatePairIntrinsicIncidence.fullOn_isFixedPointFreeBinary N N hBOn
  obtain ⟨a,ha,hpos⟩ := hres
  have hpos' : 0 <
      BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t
        (.inr (.inr a)) := hpos
  have hnoncritical : ¬ IsEvenCriticalSubgroup N B0 :=
    BinaryDuplicatePairIntrinsicIncidence.fullOn_not_evenCritical
      N N a ha hpos' hBOn
  let B : NoncriticalBinarySubgroups N := ⟨B0,hbinary,hnoncritical⟩
  have hpairpos : 0 <
      BinaryDuplicatePairProfileUnion.shiftedMultiplicity 1 t (pairIndex N) := by
    change 0 < t.1+1
    omega
  let s : PermutationPairOrbitMarks.PairOrbit B.val :=
    pairOrbit_of_fullOn N hBOn hpairpos
  let z : OddMarkerPairIntrinsicIncidence.MarkedFamily N := ⟨B,s⟩
  have hselected : OddMarkerPairIntrinsicIncidence.selectedProfile N z = t :=
    selectedProfile_eq_of_fullOn N B s t hBOn
  have ht : t ∈ OddMarkerPairIntrinsicIncidence.selector N :=
    Finset.mem_image.mpr ⟨z,Finset.mem_univ _,hselected⟩
  let K := relabelSubgroup e.symm H.1
  have hKOn : OrbitProfileFullOn (MarkerAction N) (Equiv.refl _) K := by
    simpa only [Equiv.self_trans_symm] using hOn.relabel e.symm
  have hK : OrbitProfileFull (MarkerAction N) 1 K :=
    (orbitProfileFullOn_iff _ _ _).mp hKOn
  let L : OddMarkerPairIntrinsicIncidence.NaturalMarkerFamily N :=
    ⟨H.1,by
      refine ⟨⟨t,ht⟩,e,K,hK,?_⟩
      exact relabelSubgroup_symm e.symm H.1⟩
  exact ⟨Sum.inr L,rfl⟩

/-- The singleton and natural-marker alternatives exhaust the odd
zero-defect family. -/
theorem mem_sector (N : ℕ) (H : ZeroFamily N) :
    H.1 ∈ Set.range (OddZeroDefectBinaryFamily.subgroup N) := by
  have hsum := marker_fixed_eq_epsilon N 1 (by omega)
    (fun L => ¬ IsCriticalSubgroup (2*N+1) L) H
  by_cases hmarker : orbitCount H.1 3 = 0
  · exact singleton_mem_sector N H hmarker
  · have hfixed : orbitCount H.1 1 = 0 := by omega
    exact marker_mem_sector N H hfixed

/-- Literal inclusion of the entire intrinsic odd zero-defect branch in
the counted two-sector physical family. -/
def zeroFamilyEmbedding (N : ℕ) :
    ZeroFamily N ↪ OddZeroDefectBinaryFamily.Family N where
  toFun H := ⟨H.1,mem_sector N H⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg (fun L : OddZeroDefectBinaryFamily.Family N => L.1) h

theorem card_le_binaryFamily (N : ℕ) :
    Nat.card (ZeroFamily N) ≤ Nat.card (OddZeroDefectBinaryFamily.Family N) :=
  Nat.card_le_card_of_injective (zeroFamilyEmbedding N)
    (zeroFamilyEmbedding N).injective

/-- The checked two-sector recurrence now bounds the actual intrinsic odd
zero-defect family. -/
theorem normalized_card_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card (ZeroFamily N) : ℝ) / exactBenchmark (2*N+1) ≤
      OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
        OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
          binaryErrorRatio (N-1) := by
  have hc : (Nat.card (ZeroFamily N) : ℝ) ≤
      Nat.card (OddZeroDefectBinaryFamily.Family N) := by
    exact_mod_cast card_le_binaryFamily N
  exact (div_le_div_of_nonneg_right hc (exactBenchmark_pos _).le).trans
    (OddZeroDefectBinaryFamily.normalized_card_le N hN)

theorem normalized_card_le_ordinaryRemainderRatio (N : ℕ) :
    (Nat.card (ZeroFamily N) : ℝ) / exactBenchmark (2*N+1) ≤
      ordinaryRemainderRatio (2*N+1) := by
  have hc : (Nat.card (ZeroFamily N) : ℝ) ≤
      Nat.card (OddZeroDefectBinaryFamily.Family N) := by
    exact_mod_cast card_le_binaryFamily N
  exact (div_le_div_of_nonneg_right hc (exactBenchmark_pos _).le).trans
    (OddZeroDefectBinaryFamily.normalized_card_le_ordinaryRemainderRatio N)

end SymmetricSubgroupAsymptotics.OddZeroDefectCoverage

end
