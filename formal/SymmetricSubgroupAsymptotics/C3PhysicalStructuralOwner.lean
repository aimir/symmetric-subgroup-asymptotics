import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity
import SymmetricSubgroupAsymptotics.Non2OwnerCapacityFrontier

/-!
# The high C3 structural owner as a complete physical predicate

The high trivial-axis theorem finds an earlier structural owner on one
literal orbit of the untouched complement.  First-owner aggregation is
instead indexed by the complete physical subgroup.  The predicate below
retains the full C3 fusion chart, the complete complement subgroup, and the
actual owned orbit pair.  It is invariant under relabelling of the complete
point set, so it can be used directly in the general non-2 owner menu.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A complete physical subgroup has a high-C3 structural owner when it has
an actual regular-C3 fusion chart whose untouched complement contains a
literal orbit pair accepted by the already constructed structural menu. -/
def C3PhysicalStructuralOwner (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (b : ℕ)
    (e : TernaryCyclic ⊕ Fin b ≃ Fin n)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))),
      relabelSubgroup e (H.map (fusionOrbitAction ternaryRegularAction)) = G ∧
      ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
        ∃ (N : Subgroup
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
          (hN : N.Normal),
          letI := hN
          TernaryHighEarlierOwner
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
            o.orbit

/-- The retained chart makes the complete physical owner invariant under an
arbitrary relabelling.  No orbit representative or abstract isomorphism
class is chosen. -/
theorem c3PhysicalStructuralOwner_relabel_iff {m n : ℕ}
    (hmn : m = n) (e : Fin m ≃ Fin n)
    (G : Subgroup (Equiv.Perm (Fin m))) :
    C3PhysicalStructuralOwner n (relabelSubgroup e G) ↔
      C3PhysicalStructuralOwner m G := by
  subst n
  constructor
  · rintro ⟨b, c, H, hc, o, N, hN, hOwner⟩
    refine ⟨b, c.trans e.symm, H, ?_, o, N, hN, hOwner⟩
    calc
      relabelSubgroup (c.trans e.symm)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e.symm
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e.symm (relabelSubgroup e G) := by rw [hc]
      _ = G := relabelSubgroup_symm e G
  · rintro ⟨b, c, H, hc, o, N, hN, hOwner⟩
    refine ⟨b, c.trans e, H, ?_, o, N, hN, hOwner⟩
    calc
      relabelSubgroup (c.trans e)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e G := by rw [hc]

/-- The singleton high-C3 predicate is a degree-natural first-owner menu. -/
def c3PhysicalStructuralOwnerMenu
    (n : ℕ) (_i : Fin 1) (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  C3PhysicalStructuralOwner n G

theorem c3PhysicalStructuralOwnerMenu_natural :
    DegreeNaturalOwnerMenu c3PhysicalStructuralOwnerMenu := by
  intro m n hmn e i G
  exact c3PhysicalStructuralOwner_relabel_iff hmn e G

/-- The classification-facing high-C3 theorem now lands on the complete
physical subgroup, with any chosen outer chart. -/
theorem c3TrivialHigh_enters_physicalStructuralOwner
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b n : ℕ)
    (e : TernaryCyclic ⊕ Fin b ≃ Fin n)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    C3PhysicalStructuralOwner n
      (relabelSubgroup e
        (H.map (fusionOrbitAction ternaryRegularAction))) := by
  obtain ⟨o, N, hN, hOwner⟩ :=
    c3TrivialHigh_enters_ternaryEarlierOwner
      hChief hWeight hPrimitive h18 b P H hH
  exact ⟨b, e, H, rfl, o, N, hN, hOwner⟩

/-- First ownership by the appended residual branch is impossible for a
high trivial-axis C3 state.  This is the first required application of the
general owner-or-capacity interface. -/
theorem not_firstOwned_residual_of_c3TrivialHigh
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b n : ℕ)
    (e : TernaryCyclic ⊕ Fin b ≃ Fin n)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ¬ FirstOwned
        (ownerOrResidualEligible c3PhysicalStructuralOwnerMenu n)
        (Fin.last 1)
        (relabelSubgroup e
          (H.map (fusionOrbitAction ternaryRegularAction))) := by
  rw [firstOwned_ownerOrResidual_last_iff]
  push Not
  refine ⟨0, ?_⟩
  exact c3TrivialHigh_enters_physicalStructuralOwner
    hChief hWeight hPrimitive h18 b n e P H hH

end SymmetricSubgroupAsymptotics

end
