import SymmetricSubgroupAsymptotics.BinaryS16CanonicalCarrierProfile

/-!
# Type-valued canonical S16 orbit realizations

`BinaryS16CanonicalCarrierProfile.Realizes` is deliberately proposition-valued,
which is sufficient for coverage and ownership.  The physical producer must
also construct charts, routed slots, and changed-block records.  This file
mirrors the seven realization constructors in `Type` and chooses one
certificate for the already deterministic checked colour.  The certificate
is a function of the literal subgroup and orbit; it is not attached as an
extra mark to the family being counted.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16CertifiedOrbitRealization

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile
open BinaryDegreeEightPhysicalAnalyticClosure

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

/-- Data-level version of one literal-orbit realization. -/
inductive CertifiedRealization (o : Orbit H) : OrbitColor → Type 2
  | c2 (e : criticalActionPoints .c2 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .c2) =
        OrbitProfileFromOrbits.orbitImage H o) :
      CertifiedRealization o .c2
  | v4 (e : criticalActionPoints .v4 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .v4) =
        OrbitProfileFromOrbits.orbitImage H o) :
      CertifiedRealization o .v4
  | d8 (e : criticalActionPoints .d8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .d8) =
        OrbitProfileFromOrbits.orbitImage H o) :
      CertifiedRealization o .d8
  | e8 (e : criticalActionPoints .e8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H o) :
      CertifiedRealization o .e8
  | cyclicFour (W : SmallOrbitWitness 4 H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      CertifiedRealization o .cyclicFour
  | carrier8
      (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      CertifiedRealization o .carrier8
  | carrier16
      (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (S : AxisSlot W.action W.axis) (hs : S.HasNoncritical) :
      CertifiedRealization o .carrier16

/-- Forgetting the data-level certificate recovers the checked structural
realization proposition. -/
def CertifiedRealization.toRealizes {o : Orbit H} {c : OrbitColor} :
    CertifiedRealization H o c → Realizes H o c
  | .c2 e he => .c2 e he
  | .v4 e he => .v4 e he
  | .d8 e he => .d8 e he
  | .e8 e he => .e8 e he
  | .cyclicFour W hpoint S hs => .cyclicFour W hpoint S hs
  | .carrier8 W hpoint S hs => .carrier8 W hpoint S hs
  | .carrier16 W hpoint S hs => .carrier16 W hpoint S hs

/-- Elimination stays in `Prop`: every proposition-valued realization has a
corresponding inhabited data-level certificate type. -/
theorem certifiedRealization_nonempty_of_realizes
    {o : Orbit H} {c : OrbitColor} (h : Realizes H o c) :
    Nonempty (CertifiedRealization H o c) := by
  cases h with
  | c2 e he => exact ⟨.c2 e he⟩
  | v4 e he => exact ⟨.v4 e he⟩
  | d8 e he => exact ⟨.d8 e he⟩
  | e8 e he => exact ⟨.e8 e he⟩
  | cyclicFour W hpoint S hs => exact ⟨.cyclicFour W hpoint S hs⟩
  | carrier8 W hpoint S hs => exact ⟨.carrier8 W hpoint S hs⟩
  | carrier16 W hpoint S hs => exact ⟨.carrier16 W hpoint S hs⟩

/-- The deterministic checked colour has a data-level realization. -/
theorem checkedCertifiedRealization_nonempty
    (hH : ResidualSector H) (o : Orbit H) :
    Nonempty (CertifiedRealization H o (checkedProfile H hH o)) :=
  certifiedRealization_nonempty_of_realizes H
    (profile_realizes H smallRegistryMixtureEquations hH o)

/-- Chosen data for the deterministic checked colour.  Choice occurs in a
function of the original subgroup and orbit and therefore creates no counted
source multiplicity. -/
def checkedCertifiedRealization
    (hH : ResidualSector H) (o : Orbit H) :
    CertifiedRealization H o (checkedProfile H hH o) :=
  Classical.choice (checkedCertifiedRealization_nonempty H hH o)

theorem checkedCertifiedRealization_realizes
    (hH : ResidualSector H) (o : Orbit H) :
    (checkedCertifiedRealization H hH o).toRealizes =
      profile_realizes H smallRegistryMixtureEquations hH o := by
  apply Subsingleton.elim

end SymmetricSubgroupAsymptotics.BinaryS16CertifiedOrbitRealization

end
