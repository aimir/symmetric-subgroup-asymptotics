import SymmetricSubgroupAsymptotics.BinaryCarrierS16CertifiedAxisRouting
import SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

/-!
# Direct Type-valued certified orbit profile for the S16 residual sector

This file constructs the physical orbit profile directly from
`ResidualSector`.  It does not first choose the proposition-valued
`checkedProfile` and does not compare a later certificate to that choice.

The four critical constructors retain their literal orbit charts.  Each
positive constructor retains the corresponding physical orbit witness, the
equality identifying its quotient-orbit point, and a numerically certified
exact-axis slot.  Existence is first proved in `Prop` as `Nonempty`; a single
classical choice then gives the Type-valued profile used by the physical word.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectCertifiedOrbitProfile

open SymmetricSubgroupAsymptotics
open BinaryCarrierCertifiedRetention
open BinaryCarrierProfileTransport
open BinaryCarrierS16CertifiedAxisRouting
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryCarrierS16RouteLocalCertificates
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryS16CanonicalCarrierProfile

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

/-! ## The missing certified width-four branch -/

/-- The complete four-point registry gives either the canonical certified C4
slot or a literal critical orbit chart. -/
theorem widthFour_certified_or_critical
    (B : SmallRegistryMixtureEquations) (hbinary : IsPGroup 2 H)
    (o : Orbit H) (hcard : Nat.card o.orbit = 4) :
    let W := smallWitness H hbinary 4 o hcard
    Nonempty (CertifiedPositiveAxisSlot W.axis 2) ∨
      (∃ i : CriticalActionKind,
        ∃ e : criticalActionPoints i ≃ o.orbit,
          relabelSubgroup e (criticalActionSubgroup i) =
            OrbitProfileFromOrbits.orbitImage H o) := by
  let W := smallWitness H hbinary 4 o hcard
  have htrans : PermutationSubgroupTransitive W.action := by
    intro x y
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq W.action x y
    exact ⟨u,u.property,hu⟩
  obtain ⟨k,g,hg⟩ := BinaryMenuSmallCoverage.width4_complete
    W.action W.action_binary htrans
  let e := (B.point4 k).trans g.symm
  have he : relabelSubgroup e (mixtureAction (smallKind4 k)) = W.action :=
    small_relabel_of_registry H W g hg (B.point4 k) (B.image4 k)
  fin_cases k
  · left
    let S := W.quotientIdentityAxisSlot (.inr none) e he
    refine ⟨CertifiedPositiveAxisSlot.ofCertificate
      (old := 2) (retained := 2) S ?_ ?_ (by omega) (by omega)⟩
    · change ∃ c : Fin 1, ∃ t, (smallKind4 0) = .inr t
      exact ⟨0,none,rfl⟩
    · exact cyclicFourAxisSlot_certificate W e he
  · right
    refine ⟨.v4,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .v4 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,smallWitness]
      exact Quotient.out_eq' o
    exact criticalChart_transport H .v4 hpoint hc
  · right
    refine ⟨.d8,?_⟩
    have hc := W.criticalOrbit_of_relabel_quotient .d8 e he
    have hpoint : Quotient.mk'' W.point = o := by
      dsimp [W,smallWitness]
      exact Quotient.out_eq' o
    exact criticalChart_transport H .d8 hpoint hc

/-! ## Type-valued orbit certificates -/

/-- Complete data carried by one literal orbit in the residual sector. -/
inductive OrbitCertificate (o : Orbit H) : Type 2
  | c2 (e : criticalActionPoints .c2 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .c2) =
        OrbitProfileFromOrbits.orbitImage H o) : OrbitCertificate o
  | v4 (e : criticalActionPoints .v4 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .v4) =
        OrbitProfileFromOrbits.orbitImage H o) : OrbitCertificate o
  | d8 (e : criticalActionPoints .d8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .d8) =
        OrbitProfileFromOrbits.orbitImage H o) : OrbitCertificate o
  | e8 (e : criticalActionPoints .e8 ≃ o.orbit)
      (he : relabelSubgroup e (criticalActionSubgroup .e8) =
        OrbitProfileFromOrbits.orbitImage H o) : OrbitCertificate o
  | cyclicFour (W : SmallOrbitWitness 4 H)
      (hpoint : Quotient.mk'' W.point = o)
      (route : DegreeFourRoute W) :
      OrbitCertificate o
  | carrier8
      (W : BinaryDegreeEightNormalizerSaturatedDirect.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (route : DegreeEightRoute W.action W.axis) :
      OrbitCertificate o
  | carrier16
      (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)
      (hpoint : Quotient.mk'' W.point = o)
      (route : DegreeSixteenRoute W.action W.axis) :
      OrbitCertificate o

/-- The seven-colour label read from the certificate itself. -/
def OrbitCertificate.color {o : Orbit H} : OrbitCertificate H o → OrbitColor
  | .c2 _ _ => .c2
  | .v4 _ _ => .v4
  | .d8 _ _ => .d8
  | .e8 _ _ => .e8
  | .cyclicFour _ _ _ => .cyclicFour
  | .carrier8 _ _ _ => .carrier8
  | .carrier16 _ _ _ => .carrier16

/-- Forgetting numerical certification gives the original structural
realization proposition for the certificate's own colour. -/
def OrbitCertificate.toRealizes {o : Orbit H}
    (C : OrbitCertificate H o) : Realizes H o C.color := by
  cases C with
  | c2 e he => exact .c2 e he
  | v4 e he => exact .v4 e he
  | d8 e he => exact .d8 e he
  | e8 e he => exact .e8 e he
  | cyclicFour W hpoint R =>
      exact .cyclicFour W hpoint R.certified.axisSlot R.certified.hasNoncritical
  | carrier8 W hpoint R =>
      exact .carrier8 W hpoint R.certified.axisSlot R.certified.hasNoncritical
  | carrier16 W hpoint R =>
      exact .carrier16 W hpoint R.certified.axisSlot R.certified.hasNoncritical

/-! ## Direct construction from the residual-sector hypotheses -/

/-- Every literal orbit has a complete Type-valued certificate.  The theorem
returns `Nonempty`, so all eliminations of proposition-valued classification
theorems remain in `Prop`. -/
theorem orbitCertificate_nonempty
    (hH : ResidualSector H) (o : Orbit H) :
    Nonempty (OrbitCertificate H o) := by
  rcases orbit_card_cases H hH.binary hH.noFixedPoints o (hH.orbit_le o) with
    h2 | h4 | h8 | h16
  · obtain ⟨_,e,he⟩ :=
      width2_identitySlot_and_critical H smallRegistryMixtureEquations
        hH.binary o h2
    exact ⟨.c2 e he⟩
  · rcases widthFourRoute_nonempty_or_critical H smallRegistryMixtureEquations
      hH.binary o h4 with hs | hc
    · let W := smallWitness H hH.binary 4 o h4
      change Nonempty (DegreeFourRoute W) at hs
      obtain ⟨R⟩ := hs
      refine ⟨.cyclicFour W ?_ R⟩
      dsimp [W,smallWitness]
      exact Quotient.out_eq' o
    · obtain ⟨i,e,he⟩ := hc
      cases i with
      | c2 => exact ⟨.c2 e he⟩
      | v4 => exact ⟨.v4 e he⟩
      | d8 => exact ⟨.d8 e he⟩
      | e8 => exact ⟨.e8 e he⟩
  · let W := witness8 H hH.binary o h8
    have hres : H ∈ D8.carrierResidualFamily n := ⟨⟨W⟩,hH.noDirect8⟩
    rcases degreeEightResidualRoute_nonempty_or_isE8Orbit hres W with
      hs | he8
    · obtain ⟨R⟩ := hs
      refine ⟨.carrier8 W ?_ R⟩
      dsimp [W,witness8]
      exact Quotient.out_eq' o
    · obtain ⟨e,he⟩ := he8
      have hpoint : Quotient.mk'' W.point = o := by
        dsimp [W,witness8]
        exact Quotient.out_eq' o
      obtain ⟨e',he'⟩ :=
        criticalChart_transport H .e8 hpoint ⟨e,he⟩
      exact ⟨.e8 e' he'⟩
  · let W := witness16 H hH.binary o h16
    have hres : H ∈ D16.carrierResidualFamily n := ⟨⟨W⟩,hH.noDirect16⟩
    obtain ⟨R⟩ := degreeSixteenResidualRoute_nonempty hres W
    refine ⟨.carrier16 W ?_ R⟩
    dsimp [W,witness16]
    exact Quotient.out_eq' o

/-- The new deterministic physical profile.  Its certificate and colour are
chosen together, directly from the residual-sector classification. -/
def profile (hH : ResidualSector H) (o : Orbit H) : OrbitCertificate H o :=
  Classical.choice (orbitCertificate_nonempty H hH o)

/-- The colour associated to the new Type-valued profile. -/
def profileColor (hH : ResidualSector H) (o : Orbit H) : OrbitColor :=
  (profile H hH o).color

/-- The chosen certificate realizes its own chosen colour. -/
theorem profile_realizes (hH : ResidualSector H) (o : Orbit H) :
    Realizes H o (profileColor H hH o) :=
  (profile H hH o).toRealizes

end SymmetricSubgroupAsymptotics.BinaryS16DirectCertifiedOrbitProfile

end
