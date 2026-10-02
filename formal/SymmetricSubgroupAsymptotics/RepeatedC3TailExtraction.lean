import SymmetricSubgroupAsymptotics.RepeatedC3TailProfile
import SymmetricSubgroupAsymptotics.OutsideOrbitTernaryChart
import SymmetricSubgroupAsymptotics.TernaryNoSmallOrbitRank
import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity

/-!
# Extracting every literal regular C3 orbit

The regular triples of one original permutation subgroup are gathered into
one repeated original-action color.  All remaining literal orbits are kept
together in a single tail point set.  This construction never chooses a
second subgroup and never replaces the tail by an abstract group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedC3TailExtraction

variable {X : Type} [Fintype X] (G : Subgroup (Equiv.Perm X))

abbrev Orbit := OrbitProfileFromOrbits.Orbit G
abbrev RegularOrbit := {o : Orbit G // IsRegularC3Orbit G o}
abbrev TailOrbit := {o : Orbit G // ¬ IsRegularC3Orbit G o}

abbrev TailPoint := Σ o : TailOrbit G, o.1.orbit

local instance regularOrbitFintype : Fintype (RegularOrbit G) :=
  Fintype.ofFinite _

local instance tailOrbitFintype : Fintype (TailOrbit G) :=
  Fintype.ofFinite _

local instance tailPointFintype : Fintype (TailPoint G) :=
  Fintype.ofFinite _

/-- A regular ternary orbit has the exact original regular-C3 chart. -/
theorem regularOrbit_chart (o : RegularOrbit G) :
    ∃ e : TernaryCyclic ≃ o.1.orbit,
      relabelSubgroup e ternaryRegularAction =
        OrbitProfileFromOrbits.orbitImage G o.1 := by
  letI : Fintype o.1.orbit := Fintype.ofFinite _
  let e₀ : Fin 3 ≃ o.1.orbit :=
    (Finite.equivFinOfCardEq o.2.1).symm
  let A : Subgroup (Equiv.Perm (Fin 3)) :=
    relabelSubgroup e₀.symm (OrbitProfileFromOrbits.orbitImage G o.1)
  have htrans : PermutationSubgroupTransitive A := by
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (e₀ x) (e₀ y)
    let a : A := ⟨e₀.symm.permCongr
      (MulAction.toPermHom G o.1.orbit g), by
        change _ ∈ (OrbitProfileFromOrbits.orbitImage G o.1).map
          e₀.symm.permCongrHom.toMonoidHom
        exact ⟨MulAction.toPermHom G o.1.orbit g, ⟨g,rfl⟩, rfl⟩⟩
    refine ⟨a, a.2, ?_⟩
    change e₀.symm (g • e₀ x) = y
    rw [hg, e₀.symm_apply_apply]
  have hp : IsPGroup 3 A := by
    exact o.2.2.map e₀.symm.permCongrHom.toMonoidHom
  have hproper : A ≠ ⊤ := by
    intro htop
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have hcard : Nat.card A = 6 := by
      rw [htop, Subgroup.card_top]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [hcard] at hk
    have hk0 : k = 0 ∨ k = 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have hpow : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk2
      rw [← hk] at hpow
      norm_num at hpow
    rcases hk0 with rfl | rfl <;> norm_num at hk
  have hA : A = alternatingGroup (Fin 3) :=
    RepeatedMarkerOwnerBound.transitive_proper_degreeThree_eq_alternating
      A htrans hproper
  let e : TernaryCyclic ≃ o.1.orbit :=
    RepeatedMarkerOwnerBound.ternaryFinEquiv.trans e₀
  refine ⟨e, ?_⟩
  calc
    relabelSubgroup e ternaryRegularAction =
        relabelSubgroup e₀
          (relabelSubgroup RepeatedMarkerOwnerBound.ternaryFinEquiv
            ternaryRegularAction) :=
      (relabelSubgroup_trans _ _ _).symm
    _ = relabelSubgroup e₀ (alternatingGroup (Fin 3)) := by
      rw [RepeatedMarkerOwnerBound.relabel_ternaryRegularAction_eq_alternating]
    _ = relabelSubgroup e₀ A := by rw [hA]
    _ = OrbitProfileFromOrbits.orbitImage G o.1 :=
      relabelSubgroup_symm e₀.symm _

/-- The complementary point set is acted on through the literal original
group, with the nonregular orbit label fixed. -/
def tailRepresentation : G →* Equiv.Perm (TailPoint G) :=
  MulAction.toPermHom G (TailPoint G)

def tailImage : Subgroup (Equiv.Perm (TailPoint G)) :=
  (tailRepresentation G).range

/-- A tail-image orbit, viewed as its literal original nonregular orbit. -/
def ambientOrbit
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) : TailOrbit G :=
  q.out.1

/-- The tail action fixes the retained original-orbit tag. -/
theorem orbit_tag_eq
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) (y : q.orbit) :
    y.1.1 = q.out.1 := by
  have hy : y.1 ∈ MulAction.orbit (tailImage G) q.out := by
    rw [← q.orbit_eq_orbit_out Quotient.out_eq']
    exact y.2
  obtain ⟨g,hg⟩ := hy
  obtain ⟨h,hh⟩ := g.2
  have hfirst : (g • q.out).1 = q.out.1 := by
    change ((g : Equiv.Perm (TailPoint G)) q.out).1 = q.out.1
    rw [← hh]
    rfl
  exact (congrArg Sigma.fst hg).symm.trans hfirst

/-- The tail orbit and the corresponding original orbit have the same
literal points after forgetting the retained nonregular-orbit tag. -/
def orbitEquiv
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) :
    q.orbit ≃ (ambientOrbit G q).1.orbit := by
  let f : q.orbit → (ambientOrbit G q).1.orbit := fun y =>
    ⟨y.1.2.1, by
      change y.1.2.1 ∈ (ambientOrbit G q).1.orbit
      rw [ambientOrbit, ← orbit_tag_eq G q y]
      exact y.1.2.2⟩
  let inv : (ambientOrbit G q).1.orbit → q.orbit := fun z =>
    ⟨⟨q.out.1, ⟨z.1, by
        simpa only [ambientOrbit] using z.2⟩⟩, by
      rw [q.orbit_eq_orbit_out Quotient.out_eq']
      have hz : z.1 ∈ MulAction.orbit G q.out.2.1 := by
        let x : q.out.1.1.orbit := q.out.2
        let z' : q.out.1.1.orbit :=
          ⟨z.1, by simpa only [ambientOrbit] using z.2⟩
        obtain ⟨h,hh⟩ := MulAction.exists_smul_eq G x z'
        exact ⟨h, congrArg Subtype.val hh⟩
      obtain ⟨h,hh⟩ := hz
      let g : tailImage G := ⟨tailRepresentation G h, ⟨h,rfl⟩⟩
      refine ⟨g, ?_⟩
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hh))⟩
  exact
    { toFun := f
      invFun := inv
      left_inv := by
        rintro ⟨⟨o,x⟩,hy⟩
        apply Subtype.ext
        have htag := orbit_tag_eq G q ⟨⟨o,x⟩,hy⟩
        change o = q.out.1 at htag
        subst o
        dsimp only [inv, f]
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }

@[simp] theorem orbitEquiv_val
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) (y : q.orbit) :
    ((orbitEquiv G q y : (ambientOrbit G q).1.orbit) : X) = y.1.2.1 := rfl

/-- Restriction to corresponding tail and original orbits is conjugate for
every original group element. -/
theorem orbitEquiv_action
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) (h : G) :
    (orbitEquiv G q).permCongr
        (MulAction.toPermHom (tailImage G) q.orbit
          ⟨tailRepresentation G h, ⟨h,rfl⟩⟩) =
      MulAction.toPermHom G (ambientOrbit G q).1.orbit h := by
  apply Equiv.ext
  intro z
  obtain ⟨y,rfl⟩ := (orbitEquiv G q).surjective z
  apply Subtype.ext
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, orbitEquiv_val]
  rfl

/-- The complete action image on a tail orbit is its original ambient
action image after the literal point equivalence. -/
theorem relabel_orbitImage
    (q : OrbitProfileFromOrbits.Orbit (tailImage G)) :
    relabelSubgroup (orbitEquiv G q)
        (OrbitProfileFromOrbits.orbitImage (tailImage G) q) =
      OrbitProfileFromOrbits.orbitImage G (ambientOrbit G q).1 := by
  ext v
  constructor
  · intro hv
    rw [mem_relabelSubgroup] at hv
    obtain ⟨g,hg⟩ := hv
    obtain ⟨h,hh⟩ := g.2
    let h' : G := h
    refine ⟨h', ?_⟩
    have hge : g = (⟨tailRepresentation G h', ⟨h',rfl⟩⟩ : tailImage G) :=
      Subtype.ext hh.symm
    subst g
    rw [← orbitEquiv_action G q h', hg]
    exact ((orbitEquiv G q).permCongr).apply_symm_apply v
  · rintro ⟨h,rfl⟩
    apply (mem_relabelSubgroup (orbitEquiv G q)
      (OrbitProfileFromOrbits.orbitImage (tailImage G) q) _).mpr
    let g : tailImage G := ⟨tailRepresentation G h, ⟨h,rfl⟩⟩
    refine ⟨g, ?_⟩
    apply ((orbitEquiv G q).permCongr).injective
    rw [orbitEquiv_action G q h]
    exact (((orbitEquiv G q).permCongr).apply_symm_apply _).symm

/-- The tail has exactly the original nonregular orbits and inherits the
absence of natural A4 orbits. -/
theorem tailImage_noSmallOrbits
    (hnoA4 : ∀ o : Orbit G,
      ¬ IsNaturalA4Action (OrbitProfileFromOrbits.orbitImage G o) o.orbit) :
    NoRegularC3OrNaturalA4Orbits (tailImage G) := by
  intro q
  constructor
  · intro hregular
    apply (ambientOrbit G q).2
    refine ⟨(Nat.card_congr (orbitEquiv G q)).symm.trans hregular.1, ?_⟩
    have hp := hregular.2.map (orbitEquiv G q).permCongrHom.toMonoidHom
    change IsPGroup 3
      (relabelSubgroup (orbitEquiv G q)
        (OrbitProfileFromOrbits.orbitImage (tailImage G) q)) at hp
    rwa [relabel_orbitImage G q] at hp
  · intro hA4
    have hA4' := TernaryHighEarlierOwner.naturalA4_relabel
      (orbitEquiv G q) (OrbitProfileFromOrbits.orbitImage (tailImage G) q) hA4
    rw [relabel_orbitImage G q] at hA4'
    exact hnoA4 (ambientOrbit G q).1 hA4'

end RepeatedC3TailExtraction
end SymmetricSubgroupAsymptotics

end
