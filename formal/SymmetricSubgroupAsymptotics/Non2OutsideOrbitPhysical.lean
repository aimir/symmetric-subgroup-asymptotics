import SymmetricSubgroupAsymptotics.Non2TransitiveActionClasses
import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart
import SymmetricSubgroupAsymptotics.OrdinaryRemainderNaturality
import SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-!
# Physical installation of every original non-2 outside orbit

An exact chart of one literal non-2 orbit is installed in its chosen
permutation-conjugacy representative family.  The deleted model retains the
entire complementary action and every correlation with it.  The local
predicate is the original ordinary-remainder condition on the same labelled
`Fin n` set.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The ordinary-remainder predicate on the canonical arbitrary-width chart
of `Fin n`. -/
def fusionWidthOrdinaryRemainderPredicate {w n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hn : w ≤ n)
    (L : Subgroup (U × Equiv.Perm (Fin (n-w)))) : Prop :=
  ¬ IsCriticalSubgroup n
    (relabelSubgroup (fusionWidthPointEquiv w n hn)
      (L.map (fusionOrbitAction (Z := Fin (n-w)) U)))

theorem fusionWidthOrdinaryRemainderPredicate_natural {w n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hn : w ≤ n) :
    FusionOrbitNatural U (fusionWidthOrdinaryRemainderPredicate U hn) :=
  fusionOrbitNatural_of_relabel_invariant U
    (fusionWidthPointEquiv w n hn)
    (fun H => ¬ IsCriticalSubgroup n H)
    (fun s H => ordinaryRemainder_relabel_iff n s H)

/-- An exact chart of any literal orbit puts the complete original ordinary
subgroup into the corresponding canonical width family. -/
theorem FusionOrbitProfileChart.mem_widthCanonicalFamily_ordinary
    {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ¬ IsCriticalSubgroup n H)
    (o : OrbitProfileFromOrbits.Orbit H)
    (hw : Nat.card o.orbit = w) (hn : w ≤ n)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (eO : Fin w ≃ o.orbit)
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H o) :
    H ∈ FusionWidthCanonicalFamily U hn
      (fusionWidthOrdinaryRemainderPredicate U hn) := by
  have hsplit := PermutationCharacterRankSplit.card_split
    (FusionOrbitProfileChart.orbitSubaction H o)
  have hcomp : Nat.card
      ↥((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) = n-w := by
    change Nat.card o.orbit + Nat.card
      ↥((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) =
        Nat.card (Fin n) at hsplit
    rw [hw, Nat.card_fin] at hsplit
    omega
  let eC : Fin (n-w) ≃
      ↥((FusionOrbitProfileChart.orbitSubaction H o)ᶜ) :=
    (Finite.equivFinOfCardEq hcomp).symm
  let e := FusionOrbitProfileChart.chart H o eO eC
  let K : Subgroup (Equiv.Perm (Fin w ⊕ Fin (n-w))) :=
    relabelSubgroup e.symm H
  have hblock := FusionOrbitProfileChart.chart_preserves H o eO eC
  have hprojection := FusionOrbitProfileChart.chart_projection_eq
    H o U eO eC himage
  have hlocal : fusionWidthOrdinaryRemainderPredicate U hn
      (fusionDeletedModel U K) := by
    have hrec := fusionDeletedModel_recovers U K hblock hprojection
    unfold fusionWidthOrdinaryRemainderPredicate
    rw [hrec]
    change ¬ IsCriticalSubgroup n
      (relabelSubgroup (fusionWidthPointEquiv w n hn)
        (relabelSubgroup e.symm H))
    rw [relabelSubgroup_trans]
    exact (ordinaryRemainder_relabel_iff n
      (e.symm.trans (fusionWidthPointEquiv w n hn)) H).mpr hH
  exact fusionWidthCanonicalFamily_of_chart U hn H e hblock hprojection
    (fusionWidthOrdinaryRemainderPredicate U hn) hlocal

namespace RepeatedMarkerOwnerBound

/-- Every marked outside orbit, in its exact degree, enters one canonical
non-2 action family with the complete ordinary subgroup retained. -/
theorem outsideOrbit_mem_non2CanonicalFamily {n w : ℕ}
    (H : OrdinaryRemainderSubgroups n) (o : OutsideOrbit H.1)
    (hw : Nat.card o.1.orbit = w) (hn : w ≤ n) :
    ∃ i : Non2TransitiveActionClass (Fin w),
      H.1 ∈ FusionWidthCanonicalFamily i.representative hn
        (fusionWidthOrdinaryRemainderPredicate i.representative hn) := by
  obtain ⟨i,eO,himage⟩ := Non2TransitiveActionClass.orbit_cover
    H.1 o.1 hw o.2.1
  exact ⟨i, FusionOrbitProfileChart.mem_widthCanonicalFamily_ordinary
    H.1 H.2 o.1 hw hn i.representative eO himage⟩

end RepeatedMarkerOwnerBound

end SymmetricSubgroupAsymptotics

end
