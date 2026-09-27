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
    change (h : Equiv.Perm (Fin (2*N+1))) z = z
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

end SymmetricSubgroupAsymptotics.OddZeroDefectCoverage

end
