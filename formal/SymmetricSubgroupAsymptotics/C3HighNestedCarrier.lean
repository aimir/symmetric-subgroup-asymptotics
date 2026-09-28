import SymmetricSubgroupAsymptotics.C3HighOrbitDichotomy
import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart
import SymmetricSubgroupAsymptotics.FusionWidthPhysical
import SymmetricSubgroupAsymptotics.OutsideOrbitTernaryChart

/-!
# Nested physical carriers inside the high regular-C3 branch

The high trivial-axis branch produces an orbit of the literal complement
source.  This file lifts that orbit to the whole physical subgroup on
`TernaryCyclic ⊕ Fin b`.  The outer regular-C3 block remains literally in
the complementary carrier.  The selected normal subgroup and its strict
high inequality are retained in `C3HighNestedCarrier.Data`.

No owner recognition or numerical estimate is used here.  Once an action on
the selected orbit has been labelled by `Fin w`, the last theorem places the
whole physical subgroup in the corresponding arbitrary-width canonical
fusion family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C3HighNestedCarrier

variable {b : ℕ}

/-- The whole labelled physical subgroup represented by a local regular-C3
state. -/
abbrev physicalSubgroup
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) :
    Subgroup (Equiv.Perm (TernaryCyclic ⊕ Fin b)) :=
  H.map (fusionOrbitAction ternaryRegularAction)

/-- The structural data extracted from the high branch.  Unlike the earlier
owner wrapper, this record retains the actual normal subgroup and the strict
high inequality. -/
structure Data (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))) where
  orbit : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)
  normal : Subgroup
    (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) orbit)
  normal_normal : normal.Normal
  high : letI := normal_normal
    3 * Nat.card orbit.orbit <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 normal)

/-- The high-state extractor, with no loss of the normal pair or highness. -/
theorem exists_data
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) : Nonempty (Data H) := by
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  exact ⟨⟨o, N, hN, hhigh⟩⟩

variable (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))

/-- The orbit in the whole physical subgroup represented by a selected orbit
of the complement source. -/
def liftedOrbit
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) :
    OrbitProfileFromOrbits.Orbit (physicalSubgroup H) :=
  Quotient.mk'' (Sum.inr o.out)

/-- The selected complement orbit and its lift have the same literal points,
with only the `Sum.inr` inclusion added. -/
def orbitEquiv
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) :
    o.orbit ≃ (liftedOrbit H o).orbit := by
  let f : o.orbit → (liftedOrbit H o).orbit := fun a =>
    ⟨Sum.inr a.1, by
      rw [liftedOrbit, MulAction.orbitRel.Quotient.orbit_mk]
      have ha : a.1 ∈ MulAction.orbit (C3ComplementSource b H) o.out := by
        rw [← o.orbit_eq_orbit_out Quotient.out_eq']
        exact a.property
      obtain ⟨g, hg⟩ := ha
      obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp g.property
      refine ⟨⟨fusionOrbitAction ternaryRegularAction u,
        Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩, ?_⟩
      change Sum.inr (u.2 o.out) = Sum.inr a.1
      apply congrArg Sum.inr
      change u.2 o.out = a.1
      have hug' : u.2 = (g : Equiv.Perm (Fin b)) := hug
      rw [hug']
      exact hg
    ⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a c hac
    apply Subtype.ext
    exact Sum.inr.inj (congrArg Subtype.val hac)
  · intro z
    have hz : z.1 ∈ MulAction.orbit (physicalSubgroup H) (Sum.inr o.out) := by
      rw [← MulAction.orbitRel.Quotient.orbit_mk]
      exact z.property
    obtain ⟨k, hk⟩ := hz
    obtain ⟨u, hu, huk⟩ := Subgroup.mem_map.mp k.property
    let g : C3ComplementSource b H :=
      ⟨u.2, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩
    let a : o.orbit := ⟨u.2 o.out, by
      rw [o.orbit_eq_orbit_out Quotient.out_eq']
      exact ⟨g, rfl⟩⟩
    refine ⟨a, Subtype.ext ?_⟩
    change Sum.inr (u.2 o.out) = z.1
    have hk' : fusionOrbitAction ternaryRegularAction u (Sum.inr o.out) = z.1 := by
      change (k : Equiv.Perm (TernaryCyclic ⊕ Fin b)) (Sum.inr o.out) = z.1 at hk
      rw [← huk] at hk
      exact hk
    exact hk'

@[simp] theorem orbitEquiv_val
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) (a : o.orbit) :
    ((orbitEquiv H o a : (liftedOrbit H o).orbit) : TernaryCyclic ⊕ Fin b) =
      Sum.inr a.1 := rfl

/-- Restriction to the lifted orbit is conjugate to restriction to the
original complement-source orbit for every actual lift in the local group. -/
theorem orbitEquiv_action
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (u : ternaryRegularAction × Equiv.Perm (Fin b)) (hu : u ∈ H) :
    (orbitEquiv H o).permCongr
        (MulAction.toPermHom (C3ComplementSource b H) o.orbit
          ⟨u.2, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩) =
      MulAction.toPermHom (physicalSubgroup H) (liftedOrbit H o).orbit
        ⟨fusionOrbitAction ternaryRegularAction u,
          Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩ := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (orbitEquiv H o).surjective z
  apply Subtype.ext
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

/-- The complete permutation image on the lifted orbit is exactly the
relabelled original complement-source image. -/
theorem relabel_orbitImage
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) :
    relabelSubgroup (orbitEquiv H o)
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) =
      OrbitProfileFromOrbits.orbitImage (physicalSubgroup H) (liftedOrbit H o) := by
  ext v
  constructor
  · intro hv
    rw [mem_relabelSubgroup] at hv
    obtain ⟨g, hg⟩ := hv
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp g.property
    have hgu :
        (⟨u.2, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩ : C3ComplementSource b H) = g :=
      Subtype.ext hug
    refine ⟨⟨fusionOrbitAction ternaryRegularAction u,
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩, ?_⟩
    rw [← orbitEquiv_action H o u hu]
    rw [hgu, hg]
    exact ((orbitEquiv H o).permCongr).apply_symm_apply v
  · rintro ⟨k, rfl⟩
    obtain ⟨u, hu, huk⟩ := Subgroup.mem_map.mp k.property
    let g : C3ComplementSource b H :=
      ⟨u.2, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩
    have hk : k =
        (⟨fusionOrbitAction ternaryRegularAction u,
          Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩ : physicalSubgroup H) :=
      Subtype.ext huk.symm
    subst k
    apply (mem_relabelSubgroup (orbitEquiv H o)
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) _).mpr
    refine ⟨g, ?_⟩
    apply ((orbitEquiv H o).permCongr).injective
    rw [orbitEquiv_action H o u hu]
    exact (((orbitEquiv H o).permCongr).apply_symm_apply _).symm

/-- The lifted carrier consists exactly of the inner complement orbit, placed
in the right summand. -/
theorem liftedOrbit_eq_range
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) :
    (liftedOrbit H o).orbit =
      Set.range (fun a : o.orbit => (Sum.inr a.1 : TernaryCyclic ⊕ Fin b)) := by
  ext x
  constructor
  · intro hx
    let z : (liftedOrbit H o).orbit := ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (orbitEquiv H o).surjective z
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact (orbitEquiv H o a).property

/-- The inner orbit degree is unchanged by adjoining the outer regular-C3
block. -/
theorem liftedOrbit_card
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H)) :
    Nat.card (liftedOrbit H o).orbit = Nat.card o.orbit :=
  (Nat.card_congr (orbitEquiv H o)).symm

/-- The untouched part of the original complement has exactly `b-w` points. -/
theorem innerComplement_card {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) :
    Nat.card ↑((FusionOrbitProfileChart.orbitSubaction
      (C3ComplementSource b H) o)ᶜ) = b - w := by
  have h := PermutationCharacterRankSplit.card_split
    (FusionOrbitProfileChart.orbitSubaction (C3ComplementSource b H) o)
  change Nat.card o.orbit +
      Nat.card ↑((FusionOrbitProfileChart.orbitSubaction
        (C3ComplementSource b H) o)ᶜ) = Nat.card (Fin b) at h
  rw [hw, Nat.card_fin] at h
  omega

def innerComplementEquiv {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) :
    Fin (b - w) ≃ ↑((FusionOrbitProfileChart.orbitSubaction
      (C3ComplementSource b H) o)ᶜ) :=
  (Finite.equivFinOfCardEq (innerComplement_card H o hw)).symm

/-- Before the final finite labelling, the complement of the lifted orbit is
literally the old outer C3 block together with the untouched part of `Fin b`.
In particular the outer block is not absorbed into an abstract cardinality. -/
def complementSumEquiv {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) :
    TernaryCyclic ⊕ Fin (b - w) ≃
      ↑((FusionOrbitProfileChart.orbitSubaction
        (physicalSubgroup H) (liftedOrbit H o))ᶜ) where
  toFun
    | Sum.inl t => ⟨Sum.inl t, by
        change Sum.inl t ∉ (liftedOrbit H o).orbit
        rw [liftedOrbit_eq_range H o]
        rintro ⟨a, ha⟩
        exact Sum.inl_ne_inr ha.symm⟩
    | Sum.inr i =>
        let y := innerComplementEquiv H o hw i
        ⟨Sum.inr y.1, by
          change Sum.inr y.1 ∉ (liftedOrbit H o).orbit
          rw [liftedOrbit_eq_range H o]
          rintro ⟨a, ha⟩
          have hay : a.1 = y.1 := Sum.inr.inj ha
          have hy : y.1 ∉ o.orbit := by
            change y.1 ∉
              (FusionOrbitProfileChart.orbitSubaction
                (C3ComplementSource b H) o : Set (Fin b))
            exact y.property
          exact hy (hay ▸ a.property)⟩
  invFun z := by
    rcases z with ⟨t, ht⟩
    rcases t with t | y
    · exact Sum.inl t
    · refine Sum.inr ((innerComplementEquiv H o hw).symm ⟨y, ?_⟩)
      change y ∉
        (FusionOrbitProfileChart.orbitSubaction
          (C3ComplementSource b H) o : Set (Fin b))
      intro hy
      have hz : Sum.inr y ∈ (liftedOrbit H o).orbit := by
        rw [liftedOrbit_eq_range H o]
        exact ⟨⟨y, hy⟩, rfl⟩
      have hznot : Sum.inr y ∉ (liftedOrbit H o).orbit := by
        change Sum.inr y ∈
          ((FusionOrbitProfileChart.orbitSubaction
            (physicalSubgroup H) (liftedOrbit H o))ᶜ :
              Set (TernaryCyclic ⊕ Fin b))
        exact ht
      exact hznot hz
  left_inv x := by
    rcases x with t | i
    · rfl
    · change Sum.inr ((innerComplementEquiv H o hw).symm
          (innerComplementEquiv H o hw i)) = Sum.inr i
      rw [Equiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨t | y, hy⟩
    · rfl
    · change Sum.inr (innerComplementEquiv H o hw
          ((innerComplementEquiv H o hw).symm ⟨y, _⟩)).1 = Sum.inr y
      rw [Equiv.apply_symm_apply]

/-- The selected orbit cannot contain more points than its original `Fin b`
source. -/
theorem width_le {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) : w ≤ b := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : o.orbit → Fin b) Subtype.val_injective
  simpa only [hw, Nat.card_fin] using h

/-- Fixed labels for the new complete complement.  Its first summand is the
original outer C3 block. -/
def restPointEquiv {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) :
    TernaryCyclic ⊕ Fin (b - w) ≃ Fin (b + 3 - w) :=
  (Equiv.sumCongr RepeatedMarkerOwnerBound.ternaryFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (by
      have hwb := width_le H o hw
      omega)))

/-- Standard finite labels for the complement, factored through the literal
`outer C3 ⊕ untouched inner complement` decomposition. -/
def complementEquiv {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) :
    Fin (b + 3 - w) ≃
      ↑((FusionOrbitProfileChart.orbitSubaction
        (physicalSubgroup H) (liftedOrbit H o))ᶜ) :=
  (restPointEquiv H o hw).symm.trans (complementSumEquiv H o hw)

/-- A chosen `Fin w` labelling of the inner orbit, lifted without changing its
original permutation image. -/
def pointEquiv {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (e : Fin w ≃ o.orbit) :
    Fin w ≃ (liftedOrbit H o).orbit :=
  e.trans (orbitEquiv H o)

theorem pointEquiv_image {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (U : Subgroup (Equiv.Perm (Fin w))) (e : Fin w ≃ o.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) :
    relabelSubgroup (pointEquiv H o e) U =
      OrbitProfileFromOrbits.orbitImage (physicalSubgroup H) (liftedOrbit H o) := by
  rw [pointEquiv, ← relabelSubgroup_trans, himage, relabel_orbitImage H o]

/-- The whole nested chart.  The first block is the selected complement
orbit; the second contains the original outer C3 block and every other point. -/
def chart {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) (e : Fin w ≃ o.orbit) :
    Fin w ⊕ Fin (b + 3 - w) ≃ TernaryCyclic ⊕ Fin b :=
  FusionOrbitProfileChart.chart (physicalSubgroup H) (liftedOrbit H o)
    (pointEquiv H o e) (complementEquiv H o hw)

/-- The outer regular-C3 block is literally present in the second chart
coordinate before the final finite relabelling. -/
theorem chart_outerC3 {w : ℕ}
    (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
    (hw : Nat.card o.orbit = w) (e : Fin w ≃ o.orbit)
    (t : TernaryCyclic) :
    chart H o hw e (Sum.inr (restPointEquiv H o hw (Sum.inl t))) = Sum.inl t := by
  rw [chart, FusionOrbitProfileChart.chart_inr]
  change ((complementEquiv H o hw (restPointEquiv H o hw (Sum.inl t)) :
    ↑((FusionOrbitProfileChart.orbitSubaction
      (physicalSubgroup H) (liftedOrbit H o))ᶜ)) :
      TernaryCyclic ⊕ Fin b) = Sum.inl t
  rw [complementEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Fixed labels for the whole outer physical point set. -/
def outerPointEquiv (b : ℕ) : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3) :=
  (Equiv.sumCongr RepeatedMarkerOwnerBound.ternaryFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

/-- The selected nested carrier places any labelling of the whole outer
physical subgroup in the arbitrary-width canonical family.  The premise is
evaluated on the exact deleted model of the chart above, so the outer C3 block
and all remaining correlations stay in the complement. -/
theorem mem_widthCanonicalFamily_of_relabel {w : ℕ}
    (C : Data H) (hw : Nat.card C.orbit.orbit = w)
    (U : Subgroup (Equiv.Perm (Fin w))) (e : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (P : Subgroup (U × Equiv.Perm (Fin (b + 3 - w))) → Prop)
    (hP : P (fusionDeletedModel U
      (relabelSubgroup (chart H C.orbit hw e).symm (physicalSubgroup H)))) :
    relabelSubgroup q (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily U (by
        have hwb := width_le H C.orbit hw
        omega) P := by
  let K := relabelSubgroup (chart H C.orbit hw e).symm (physicalSubgroup H)
  have hblock := FusionOrbitProfileChart.chart_preserves
    (physicalSubgroup H) (liftedOrbit H C.orbit)
      (pointEquiv H C.orbit e) (complementEquiv H C.orbit hw)
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    (physicalSubgroup H) (liftedOrbit H C.orbit) U
      (pointEquiv H C.orbit e) (complementEquiv H C.orbit hw)
      (pointEquiv_image H C.orbit U e himage)
  have hm : K ∈ FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P) :=
    fusionDeletedModel_mem_family U K hblock hprojection P hP
  have hr := fusionRelabelledFamily_of_chart
    (FusionOrbitModel U (FusionAcceptedOrbitPredicate U P))
    ((chart H C.orbit hw e).trans q)
    (fusionWidthPointEquiv w (b + 3) (by
      have hwb := width_le H C.orbit hw
      omega)) K hm
  have he : (chart H C.orbit hw e).symm.trans
      ((chart H C.orbit hw e).trans q) = q := by
    ext x
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  simpa only [K, FusionWidthCanonicalFamily, relabelSubgroup_trans, he] using hr

/-- Canonical outer labels are the common specialization used by the final
finite-width recurrence. -/
theorem mem_widthCanonicalFamily {w : ℕ}
    (C : Data H) (hw : Nat.card C.orbit.orbit = w)
    (U : Subgroup (Equiv.Perm (Fin w))) (e : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (P : Subgroup (U × Equiv.Perm (Fin (b + 3 - w))) → Prop)
    (hP : P (fusionDeletedModel U
      (relabelSubgroup (chart H C.orbit hw e).symm (physicalSubgroup H)))) :
    relabelSubgroup (outerPointEquiv b) (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily U (by
        have hwb := width_le H C.orbit hw
        omega) P :=
  mem_widthCanonicalFamily_of_relabel H C hw U e himage (outerPointEquiv b) P hP

/-- Every global label change appearing in the outer `FusionOrbitFamily` is
absorbed by the same canonical family; it introduces no extra carrier weight. -/
theorem mem_widthCanonicalFamily_of_conjugate {w : ℕ}
    (C : Data H) (hw : Nat.card C.orbit.orbit = w)
    (U : Subgroup (Equiv.Perm (Fin w))) (e : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (p : Equiv.Perm (TernaryCyclic ⊕ Fin b))
    (P : Subgroup (U × Equiv.Perm (Fin (b + 3 - w))) → Prop)
    (hP : P (fusionDeletedModel U
      (relabelSubgroup (chart H C.orbit hw e).symm (physicalSubgroup H)))) :
    relabelSubgroup (outerPointEquiv b)
        (relabelSubgroup p (physicalSubgroup H)) ∈
      FusionWidthCanonicalFamily U (by
        have hwb := width_le H C.orbit hw
        omega) P := by
  simpa only [relabelSubgroup_trans] using
    mem_widthCanonicalFamily_of_relabel H C hw U e himage
      (p.trans (outerPointEquiv b)) P hP

end C3HighNestedCarrier
end SymmetricSubgroupAsymptotics

end
