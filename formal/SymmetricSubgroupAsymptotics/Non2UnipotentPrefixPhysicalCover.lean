import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
import SymmetricSubgroupAsymptotics.Non2OwnerCapacityFrontier

/-!
# Physical cover by the fixed unipotent-prefix pair menu

The historical selected `O03/O02-resUP` state supplies an actual nonbinary
orbit with one of eight pair widths and an actual pair frame on that orbit.
This file isolates precisely that structural input.  Its witnesses remain
inside a proposition, so choosing an orbit chart, action representative, or
pair frame does not introduce a counted pointing or frame multiplicity.

No arbitrary outside-orbit selector is used: the witness is the literal
selected orbit inherited from the physical owner chain.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Proof-only structural content of the historical selected UP orbit.
The eight labels store pair count `s`; the original orbit has width `2s`. -/
def HasSelectedUPPairOrbit {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ d : PairCountLabel, ∃ o : OrbitProfileFromOrbits.Orbit H,
    Nat.card o.orbit = d.sourceDegree ∧
      ¬ IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∧
      Nonempty (BinaryPairFrame
        (OrbitProfileFromOrbits.orbitImage H o) (Fin d.pairCount))

/-- A literal selected UP orbit enters the fixed action menu and the exact
last first-owner cell.  The complete physical subgroup, its complement, and
the residual rejection by every earlier owner remain in the canonical
family; only orbit points are relabelled to the chosen action representative.
-/
theorem selectedUPPairOrbit_mem_residualCanonicalFamily
    {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (howner : FirstOwned (ownerOrResidualEligible Earlier n)
      (Fin.last r) H)
    (hUP : HasSelectedUPPairOrbit H) :
    ∃ (i : ActionIndex) (hn : i.1.sourceDegree ≤ n),
      H ∈ FusionWidthCanonicalFamily i.2.1.representative hn
        (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier)
          i.1.sourceDegree (Fin.last r, i.2.1)
            (n - i.1.sourceDegree)) := by
  rcases hUP with ⟨d, o, hw, hnon2, ⟨F⟩⟩
  have hn : d.sourceDegree ≤ n := by
    have hc := Nat.card_le_card_of_injective
      (Subtype.val : o.orbit → Fin n) Subtype.val_injective
    simpa only [hw, Nat.card_fin] using hc
  obtain ⟨a, eO, himage⟩ :=
    Non2TransitiveActionClass.orbit_cover H o hw hnon2
  have hback : relabelSubgroup eO.symm
      (OrbitProfileFromOrbits.orbitImage H o) = a.representative := by
    rw [← himage, relabelSubgroup_symm]
  let F' : BinaryPairFrame a.representative (Fin d.pairCount) :=
    hback ▸ F.relabelPoints eO.symm
  let i : ActionIndex := ⟨d, ⟨a, ⟨F'⟩⟩⟩
  refine ⟨i, hn, ?_⟩
  simpa only [i] using
    (FusionOrbitProfileChart.mem_widthCanonicalFamily_non2FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier hEarlier)
      H hordinary (Fin.last r) howner o hw hn a eO himage)

/-- Convenient residual form: rejection by all earlier owners is exactly
first ownership by the appended last branch. -/
theorem selectedUPPairOrbit_mem_residualCanonicalFamily_of_unowned
    {r n : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (hunowned : ∀ j : Fin r, ¬ Earlier n j H)
    (hUP : HasSelectedUPPairOrbit H) :
    ∃ (i : ActionIndex) (hn : i.1.sourceDegree ≤ n),
      H ∈ FusionWidthCanonicalFamily i.2.1.representative hn
        (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier)
          i.1.sourceDegree (Fin.last r, i.2.1)
            (n - i.1.sourceDegree)) :=
  selectedUPPairOrbit_mem_residualCanonicalFamily Earlier hEarlier H
    hordinary ((firstOwned_ownerOrResidual_last_iff Earlier H).2 hunowned) hUP

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
