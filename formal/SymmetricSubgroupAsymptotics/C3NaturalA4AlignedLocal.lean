import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation
import SymmetricSubgroupAsymptotics.FusionAcceptedOrbitChartAt

/-!
# The natural-A4 branch on aligned high-C3 cells is empty

Every aligned cell predicate carries the exact split c=1 source pattern of
the complete physical subgroup: one regular `C3` orbit and no natural `A4`
orbit.  Full projection onto the retained action makes that action an actual
orbit of the same complete subgroup, with its literal point chart.  For the
natural-`A4` branch this orbit is a natural `A4` orbit, contradicting the
pattern.  The canonical family is therefore empty, and its correct local
coefficient is zero.  No numerical packet estimate is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- On the exact aligned canonical family, the natural-`A4` branch has no
member at any ambient degree. -/
theorem c3HighAligned_naturalA4_family_card_eq_zero
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.naturalA4)
    (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n) :
    Nat.card (FusionWidthCanonicalFamily
      (c3HighAlignedFirstOwnerAction j) hn
      (c3HighAlignedFirstOwnerPredicate j
        (n - c3HighAlignedFirstOwnerWidth j))) = 0 := by
  let w := c3HighAlignedFirstOwnerWidth j
  let b := n - w
  let U := c3HighAlignedFirstOwnerAction j
  have hA4 : IsNaturalA4Action U (Fin w) := by
    have h := j.2.2
    rw [hkind] at h
    exact h
  letI : MulAction.IsPretransitive U (Fin w) :=
    Non2TransitiveActionClass.representative_pretransitive j.1.2.2
  have htrans : ∀ x y : Fin w, ∃ u : U, (u : Equiv.Perm (Fin w)) x = y :=
    fun x y => MulAction.exists_smul_eq U x y
  have hw : 0 < w := c3HighAlignedFirstOwnerWidth_pos j
  rw [fusionWidthCanonicalFamily_card]
  haveI : IsEmpty (FusionOrbitFamily U
      (FusionAcceptedOrbitPredicate U
        (c3HighAlignedFirstOwnerPredicate j b))) := by
    refine ⟨fun K => ?_⟩
    obtain ⟨_, ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩⟩ := K
    obtain ⟨⟨H, hH⟩, rfl⟩ := hM
    have hlocal : ordinaryFirstOwnerLocalPredicate U
        (c3PatternStructuralBranchMenu (w + b)) j.1.2.1 H := hH.2
    have hpattern : C1DegreeNineSourcePattern
        (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w + b))
          (H.map (fusionOrbitAction (Z := Fin b) U))) :=
      hlocal.2.1.2
    obtain ⟨e, himage⟩ := fusionAcceptedOrbit_physical_orbit_chart_at U
      htrans (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w + b)) H hH.1
      ⟨0, hw⟩
    have hA4orbit := TernaryHighEarlierOwner.naturalA4_relabel e U hA4
    rw [himage] at hA4orbit
    obtain ⟨_, _, _, hnoA4⟩ := hpattern
    exact hnoA4 _ hA4orbit
  exact Nat.card_of_isEmpty

/-- The natural-`A4` aligned cell satisfies the local row with coefficient
zero, in the exact form consumed by the aligned forward continuation. -/
theorem c3HighAligned_naturalA4_local_bound
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.naturalA4)
    (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n) :
    (Nat.card (FusionWidthCanonicalFamily
      (c3HighAlignedFirstOwnerAction j) hn
      (c3HighAlignedFirstOwnerPredicate j
        (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
        exactBenchmark n ≤
      0 * ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rw [c3HighAligned_naturalA4_family_card_eq_zero j hkind n hn]
  simp

end SymmetricSubgroupAsymptotics

end
