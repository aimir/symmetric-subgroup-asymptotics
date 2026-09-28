import SymmetricSubgroupAsymptotics.C1DegreeNinePatternDeletion
import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFirstFusion
import SymmetricSubgroupAsymptotics.FusionSourceRestriction
import SymmetricSubgroupAsymptotics.FusionAcceptedOrbitChartAt

/-!
# The exact c=1 pattern enters the aligned degree-nine cell

For a high-C3 nested carrier, deleting a degree-nine nonmarker orbit preserves
the unique-regular-C3/no-natural-A4 pattern.  Its exact complement image is
the source projection of the deleted model, so the numerical rank budget and
the complete first-owner predicate hold on the same physical model.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C3HighNestedCarrier

/-- The exact degree-nine chart inherits the source rank budget from the
complete one-C3 pattern. -/
theorem Data.degreeNine_deletedModel_rankBudget
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel i.representative
          (relabelSubgroup (chart H C.orbit hw eO).symm
            (physicalSubgroup H))).map
        (MonoidHom.snd i.representative
          (Equiv.Perm (Fin (b + 3 - 9))))) := by
  have hselected : ¬ IsRegularC3Orbit
      (physicalSubgroup H) (liftedOrbit H C.orbit) := by
    intro hregular
    have hcard := hregular.1
    rw [liftedOrbit_card H C.orbit, hw] at hcard
    omega
  exact hpattern.deletedModel_rankBudget hChief hPrimitive h18
    (physicalSubgroup H) (liftedOrbit H C.orbit) i.representative
    (pointEquiv H C.orbit eO) (complementEquiv H C.orbit hw)
    (pointEquiv_image H C.orbit i.representative eO himage) hselected

/-- A degree-nine high-C3 chart from the exact c=1 family enters the aligned
first-owner cell with the source budget installed in its local predicate. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily_forAction_rankBudget
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {r b : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H)))
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    relabelSubgroup q (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily i.representative (by
        have hwb := width_le H C.orbit hw
        omega)
        (FusionSourceRestrictedPredicate i.representative
          (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
          C1DegreeNineRankBudget) := by
  have hownerLocal :=
    C.deletedModel_non2FirstOwnerPredicate_forAction
      Eligible hEligible H hw q hordinary owner howner i eO himage
  have hbudget := C.degreeNine_deletedModel_rankBudget
    hChief hPrimitive h18 H hw i eO himage hpattern
  exact mem_widthCanonicalFamily_of_relabel H C hw i.representative
    eO himage q
    (FusionSourceRestrictedPredicate i.representative
      (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
      C1DegreeNineRankBudget)
    ⟨hownerLocal, hbudget⟩

/-- If the displayed outer ternary action is full, the exact one-C3 pattern
rules out a second degree-three ternary action on the retained inner orbit.
This is the width-three endpoint needed by the c=1 finite audit. -/
theorem Data.not_degreeThree_ternaryPGroup_of_pattern
    {b : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 3)
    (hfull : H.map
      (MonoidHom.fst ternaryRegularAction (Equiv.Perm (Fin b))) = ⊤)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H))
    (hP : IsPGroup 3
      (OrbitProfileFromOrbits.orbitImage
        (C3ComplementSource b H) C.orbit)) : False := by
  let G := physicalSubgroup H
  let outer : OrbitProfileFromOrbits.Orbit G :=
    Quotient.mk'' (Sum.inl (1 : TernaryCyclic))
  have hchart : ∃ e : TernaryCyclic ≃ outer.orbit,
      relabelSubgroup e ternaryRegularAction =
        OrbitProfileFromOrbits.orbitImage G outer := by
    have hchart0 :=
      fusionAcceptedOrbit_physical_orbit_chart_at ternaryRegularAction
        ternaryRegularAction_transitive (Equiv.refl _)
        H hfull (1 : TernaryCyclic)
    rw [relabelSubgroup_refl] at hchart0
    simpa only [G, outer, Equiv.refl_apply] using hchart0
  obtain ⟨eOuter, himageOuter⟩ := hchart
  have hregularOuter : IsRegularC3Orbit G outer := by
    constructor
    · calc
        Nat.card outer.orbit = Nat.card TernaryCyclic :=
          (Nat.card_congr eOuter).symm
        _ = 3 := by simp [TernaryCyclic]
    · have hregularAction : IsPGroup 3 ternaryRegularAction :=
        IsPGroup.iff_card.mpr ⟨1, by
          rw [ternaryRegularAction_card]
          norm_num⟩
      let g : ternaryRegularAction ≃*
          OrbitProfileFromOrbits.orbitImage G outer :=
        (eOuter.permCongrHom.subgroupMap ternaryRegularAction).trans
          (MulEquiv.subgroupCongr himageOuter)
      exact hregularAction.of_equiv g
  have hregularLifted : IsRegularC3Orbit G (liftedOrbit H C.orbit) := by
    constructor
    · rw [liftedOrbit_card H C.orbit, hw]
    · let eLift := orbitEquiv H C.orbit
      let g : OrbitProfileFromOrbits.orbitImage
            (C3ComplementSource b H) C.orbit ≃*
          OrbitProfileFromOrbits.orbitImage G (liftedOrbit H C.orbit) :=
        (eLift.permCongrHom.subgroupMap
          (OrbitProfileFromOrbits.orbitImage
            (C3ComplementSource b H) C.orbit)).trans
          (MulEquiv.subgroupCongr (relabel_orbitImage H C.orbit))
      exact hP.of_equiv g
  have hne : liftedOrbit H C.orbit ≠ outer := by
    intro heq
    have houterSet : outer.orbit =
        Set.range (Sum.inl : TernaryCyclic → TernaryCyclic ⊕ Fin b) := by
      change MulAction.orbit G (Sum.inl (1 : TernaryCyclic)) = _
      exact fusionOrbitAction_orbit_eq ternaryRegularAction
        ternaryRegularAction_transitive ⟨H, hfull⟩ (1 : TernaryCyclic)
    have hmemOuter : (Sum.inl (1 : TernaryCyclic) :
        TernaryCyclic ⊕ Fin b) ∈ outer.orbit := by
      rw [houterSet]
      exact ⟨1, rfl⟩
    have hmemLifted : (Sum.inl (1 : TernaryCyclic) :
        TernaryCyclic ⊕ Fin b) ∈ (liftedOrbit H C.orbit).orbit := by
      rw [heq]
      exact hmemOuter
    rw [liftedOrbit_eq_range H C.orbit] at hmemLifted
    obtain ⟨a, ha⟩ := hmemLifted
    exact Sum.inl_ne_inr ha.symm
  obtain ⟨exceptional, _, hunique, _⟩ := hpattern
  apply hne
  exact (hunique (liftedOrbit H C.orbit) hregularLifted).trans
    (hunique outer hregularOuter).symm

end C3HighNestedCarrier
end SymmetricSubgroupAsymptotics

end
