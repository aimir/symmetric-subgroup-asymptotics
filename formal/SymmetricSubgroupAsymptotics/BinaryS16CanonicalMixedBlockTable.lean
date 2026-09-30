import SymmetricSubgroupAsymptotics.BinaryCanonicalMixedBlockTable
import SymmetricSubgroupAsymptotics.BinaryS16JointOrbitData

/-!
# The canonical mixed block table of an S16 residual subgroup

Every positive degree-eight or degree-sixteen orbit contributes one record.
The record is projected from the same Type-valued route certificate used by
the canonical word, and stores the route-output chart on the actual orbit.
Critical and cyclic-four identity routes contribute no record.

The recorded orbits inject into one token of their positive old support, so
their number is at most the complete old support.  The generic sorted-table
builder then gives the canonical mixed decoration without a new marking.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable

open SymmetricSubgroupAsymptotics
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectCertifiedOrbitProfile

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : ResidualSector H)

abbrev Orbit := OrbitProfileFromOrbits.Orbit H

/-- Read the optional mixed record directly from one retained certificate. -/
def recordOfCertificate (o : Orbit H) :
    OrbitCertificate H o → Option (MixedBlockRecord N)
  | .carrier8 W hpoint R =>
      let B := R.changedBlock W hpoint
      some (.degree8 {
        leastPoint := orbitLeast H o
        route := R.tag
        targetRepresentative := fun i ↦ (B.chart i).1 })
  | .carrier16 W hpoint R =>
      let B := R.changedBlock W hpoint
      some (.degree16 {
        leastPoint := orbitLeast H o
        route := R.tag
        targetRepresentative := fun i ↦ (B.chart i).1 })
  | _ => none

/-- The route-output record of one literal orbit, when that orbit is a
positive degree-eight or degree-sixteen carrier. -/
def recordAt (o : Orbit H) : Option (MixedBlockRecord N) :=
  recordOfCertificate H o (profile H hH o)

/-- Literal orbits which contribute a mixed record. -/
abbrev RecordedOrbit := {o : Orbit H // (recordAt H hH o).isSome}

noncomputable instance recordedOrbitFintype : Fintype (RecordedOrbit H hH) :=
  Fintype.ofFinite _

/-- Extract the record certified to exist by membership in `RecordedOrbit`. -/
def recordOf (o : RecordedOrbit H hH) : MixedBlockRecord N :=
  (recordAt H hH o.1).get o.2

theorem recordAt_leastPoint {o : Orbit H} {r : MixedBlockRecord N}
    (hr : recordAt H hH o = some r) :
    r.leastPoint = orbitLeast H o := by
  generalize hp : profile H hH o = C at hr
  cases C <;> simp [recordAt,recordOfCertificate,hp] at hr
  all_goals subst r <;> rfl

@[simp] theorem recordOf_leastPoint (o : RecordedOrbit H hH) :
    (recordOf H hH o).leastPoint = orbitLeast H o.1 := by
  apply recordAt_leastPoint H hH
  exact Option.eq_some_of_isSome o.2

/-- Every recorded orbit has positive direct old support. -/
theorem recorded_oldSupport_pos (o : RecordedOrbit H hH) :
    0 < BinaryS16JointOrbitData.oldSupportAt H hH o.1 := by
  rcases o with ⟨o,ho⟩
  generalize hp : profile H hH o = C at ho ⊢
  cases C <;>
    simp [recordAt,recordOfCertificate,BinaryS16JointOrbitData.oldSupportAt,
      BinaryS16JointOrbitData.certificateOldSupport,hp] at ho ⊢

/-- Charge a recorded orbit to the first token of its positive old support. -/
def supportToken (o : RecordedOrbit H hH) :
    Σ q : Orbit H, Fin (BinaryS16JointOrbitData.oldSupportAt H hH q) :=
  ⟨o.1,⟨0,recorded_oldSupport_pos H hH o⟩⟩

theorem supportToken_injective :
    Function.Injective (supportToken H hH) := by
  intro o p hop
  exact Subtype.ext (congrArg Sigma.fst hop)

/-- The number of mixed records is bounded by the exact direct old support. -/
theorem recordedOrbit_card_le_oldSupport :
    Fintype.card (RecordedOrbit H hH) ≤
      BinaryS16JointOrbitData.oldSupport H hH := by
  calc
    Fintype.card (RecordedOrbit H hH) = Nat.card (RecordedOrbit H hH) := by
      simp
    _ ≤ Nat.card
        (Σ q : Orbit H, Fin (BinaryS16JointOrbitData.oldSupportAt H hH q)) :=
      Nat.card_le_card_of_injective (supportToken H hH)
        (supportToken_injective H hH)
    _ = ∑ q : Orbit H, BinaryS16JointOrbitData.oldSupportAt H hH q := by
      rw [Nat.card_sigma]
      simp
    _ = BinaryS16JointOrbitData.oldSupport H hH := rfl

/-- The canonical increasing mixed table projected from the direct profile. -/
def table : CanonicalMixedBlockTable N
    (BinaryS16JointOrbitData.oldSupport H hH) :=
  canonicalMixedBlockTableOfRecords
    (fun o : RecordedOrbit H hH ↦ orbitLeast H o.1)
    (by
      intro o p hop
      exact Subtype.ext (orbitLeast_injective H hop))
    (recordOf H hH)
    (recordOf_leastPoint H hH)
    (recordedOrbit_card_le_oldSupport H hH)

end SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable

end
