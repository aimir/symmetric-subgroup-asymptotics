import SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge
import SymmetricSubgroupAsymptotics.CriticalOrbitCriterion

/-!
# Canonical degree-eight carrier orbit profile

The orbit quotient of an actual permutation subgroup is already the unmarked
indexing object for its literal orbits.  This file uses the fixed
`Fintype.equivFin` enumeration of the degree-eight orbit subtype to form one
canonical finite word.  No point, orbit, chart, axis, or route is appended to
the subgroup being counted.

For a subgroup in the unmarked degree-eight carrier residual, every coordinate
of this word has a routed exact-axis slot.  The complete word either contains a
positive-support slot, or every degree-eight orbit is the original critical E8
action.  In the latter case, once the other orbit sizes have reached their
already existing critical owners, the whole subgroup is in the complete even
critical family.

This is a structural profile extraction theorem.  It deliberately does not
sum over the resulting profiles.  A counting argument must put subgroups with
the same complete action/axis/route profile into one fixed ambient cell and use
the decorated actual-source code there.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightCanonicalCarrierProfile

open SymmetricSubgroupAsymptotics
open BinaryDegreeEightNormalizerSaturatedDirect
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightCarrierSourceBridge

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

/-! ## Canonical ordering of literal degree-eight orbits -/

/-- The literal orbit quotient, restricted only by orbit size.  Binaryity is
derived below from binaryity of the whole subgroup, so the subtype has exactly
one element per actual degree-eight orbit. -/
abbrev EightOrbit :=
  {o : OrbitProfileFromOrbits.Orbit H // Nat.card o.orbit = 8}

noncomputable instance eightOrbitFintype : Fintype (EightOrbit H) :=
  Fintype.ofFinite _

/-- The fixed finite index type of the degree-eight orbit word. -/
abbrev Index := Fin (Fintype.card (EightOrbit H))

/-- A deterministic enumeration of the literal orbit quotient.  It is used to
form a dependent product, not as an additional marking of the source. -/
noncomputable def orderedOrbitEquiv : Index H ≃ EightOrbit H :=
  (Fintype.equivFin (EightOrbit H)).symm

abbrev orderedOrbit (j : Index H) : EightOrbit H :=
  orderedOrbitEquiv H j

/-- The canonical quotient representative gives an actual degree-eight orbit
witness.  Its restriction image is binary because it is a quotient of `H`. -/
def witness (hbinary : IsPGroup 2 H) (j : Index H) : OrbitWitness H where
  point := (orderedOrbit H j).1.out
  orbit_card := by
    rw [← (orderedOrbit H j).1.orbit_eq_orbit_out Quotient.out_eq']
    exact (orderedOrbit H j).2
  binary := PermutationCharacterRankSplit.image_isPGroup
    (FusionActualOrbitCharts.orbitSet H (orderedOrbit H j).1.out) 2 hbinary

/-- The E8 condition stated directly on one element of the literal orbit
quotient. -/
def OrbitIsE8 (o : OrbitProfileFromOrbits.Orbit H) : Prop :=
  ∃ e : criticalActionPoints .e8 ≃ o.orbit,
    relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H o

/-! ## One routed coordinate for every canonical degree-eight orbit -/

variable (hbinary : IsPGroup 2 H)
  (hresidual : H ∈ carrierResidualFamily n)

abbrev Action (j : Index H) : Subgroup (Equiv.Perm (Fin 8)) :=
  (witness H hbinary j).action

abbrev Axis (j : Index H) : Subgroup (Action H hbinary j) :=
  (witness H hbinary j).axis

/-- One exact routed slot on a canonical orbit coordinate, together with the
intrinsic alternative needed by the global word: positive support, or the
actual original orbit is E8. -/
structure Coordinate (j : Index H) where
  slot : AxisSlot (Action H hbinary j) (Axis H hbinary j)
  supported_or_e8 : slot.HasNoncritical ∨ OrbitIsE8 H (orderedOrbit H j).1

/-- Existence of the coordinate follows from the all-witness residual theorem.
The proposition-valued wrapper permits case analysis on the owner dichotomy
without eliminating a proposition directly into data. -/
theorem coordinate_nonempty
    (hresidual : H ∈ carrierResidualFamily n) (j : Index H) :
    Nonempty (Coordinate H hbinary j) := by
  let W := witness H hbinary j
  let O : CarrierOwner W.action W.axis :=
    carrierResidual_all_witnesses hresidual W
  rcases supportedAxisSlot_or_isE8Action O with hsupported | hE8
  · let S := Classical.choice hsupported
    exact ⟨⟨S.1,Or.inl S.2⟩⟩
  · let R := Classical.choice O.routed
    refine ⟨⟨R.originalAxisSlot,Or.inr ?_⟩⟩
    have hactual := isE8Orbit_of_isE8Action W hE8
    have hquotient : Quotient.mk'' W.point = (orderedOrbit H j).1 := by
      dsimp [W,witness]
      exact Quotient.out_eq' _
    unfold OrbitIsE8
    rw [← hquotient]
    simpa only [IsE8Orbit] using hactual

/-- Construct the coordinate by finite choice from its proposition-valued
existence theorem.  The choice is a deterministic definition and is not data
attached to a counted subgroup. -/
noncomputable def coordinate
    (hresidual : H ∈ carrierResidualFamily n) (j : Index H) :
    Coordinate H hbinary j :=
  Classical.choice (coordinate_nonempty H hbinary hresidual j)

/-- The heterogeneous slot word obtained from the complete canonically ordered
degree-eight orbit profile. -/
abbrev wordSlot (j : Index H) : BinaryCarrierWordClosure.Slot :=
  (coordinate H hbinary hresidual j).slot.slot

/-- The word has positive completed-mixture support. -/
def HasPositiveSupport : Prop :=
  ∃ j : Index H, (coordinate H hbinary hresidual j).slot.HasNoncritical

/-- Every actual degree-eight orbit is the original critical E8 action. -/
def AllE8 : Prop :=
  ∀ j : Index H, OrbitIsE8 H (orderedOrbit H j).1

/-- Exact intrinsic split of the degree-eight carrier word.  The positive
branch supplies one cell of the already fixed whole word; it does not select a
distinguished orbit as part of the counted source. -/
theorem hasPositiveSupport_or_allE8 :
    HasPositiveSupport H hbinary hresidual ∨ AllE8 H := by
  by_cases hsupported : ∃ j : Index H,
      (coordinate H hbinary hresidual j).slot.HasNoncritical
  · exact Or.inl hsupported
  · right
    intro j
    exact (coordinate H hbinary hresidual j).supported_or_e8.resolve_left
      (fun hj ↦ hsupported ⟨j,hj⟩)

/-- In the positive branch the fixed heterogeneous slot word has the precise
noncritical-cell witness required by the simultaneous carrier producer. -/
theorem word_support_of_hasPositiveSupport
    (hsupport : HasPositiveSupport H hbinary hresidual) :
    ∃ c : Σ j, BinaryCarrierWordClosure.cells
        (wordSlot H hbinary hresidual) j,
      ∃ t, BinaryCarrierWordClosure.colors
        (wordSlot H hbinary hresidual) c = .inr t := by
  obtain ⟨j,c,t,hc⟩ := hsupport
  exact ⟨⟨j,c⟩,t,hc⟩

/-! ## The all-E8 outcome is an earlier critical owner -/

/-- If all other orbit sizes have already entered their critical owners, the
all-E8 outcome is exactly the complete intrinsic critical-orbit condition. -/
theorem allCriticalOrbits_of_allE8
    (hall : AllE8 H)
    (hother : ∀ o : OrbitProfileFromOrbits.Orbit H,
      Nat.card o.orbit ≠ 8 →
        ∃ i : CriticalActionKind,
          ∃ e : criticalActionPoints i ≃ o.orbit,
            relabelSubgroup e (criticalActionSubgroup i) =
              OrbitProfileFromOrbits.orbitImage H o) :
    CriticalOrbitCriterion.AllCriticalOrbits H := by
  intro o
  by_cases ho : Nat.card o.orbit = 8
  · let q : EightOrbit H := ⟨o,ho⟩
    obtain ⟨j,hj⟩ := (orderedOrbitEquiv H).surjective q
    have hq : OrbitIsE8 H q.1 := hj ▸ hall j
    obtain ⟨e,he⟩ := hq
    exact ⟨.e8,e,he⟩
  · exact hother o ho

/-- On the even physical point set, the all-E8 branch enters the already
counted complete critical family. -/
theorem isEvenCritical_of_allE8 {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2*N))))
    (hbinary : IsPGroup 2 H)
    (hresidual : H ∈ carrierResidualFamily (2*N))
    (hall : AllE8 H)
    (hother : ∀ o : OrbitProfileFromOrbits.Orbit H,
      Nat.card o.orbit ≠ 8 →
        ∃ i : CriticalActionKind,
          ∃ e : criticalActionPoints i ≃ o.orbit,
            relabelSubgroup e (criticalActionSubgroup i) =
              OrbitProfileFromOrbits.orbitImage H o) :
    IsEvenCriticalSubgroup N H :=
  (CriticalOrbitCriterion.isEvenCritical_iff N H).2
    (allCriticalOrbits_of_allE8 H hall hother)

/-- Final owner split in the even binary setting: the canonical routed word
has positive support, or the subgroup has already entered the complete
critical family. -/
theorem hasPositiveSupport_or_isEvenCritical {N : ℕ}
    (H : Subgroup (Equiv.Perm (Fin (2*N))))
    (hbinary : IsPGroup 2 H)
    (hresidual : H ∈ carrierResidualFamily (2*N))
    (hother : ∀ o : OrbitProfileFromOrbits.Orbit H,
      Nat.card o.orbit ≠ 8 →
        ∃ i : CriticalActionKind,
          ∃ e : criticalActionPoints i ≃ o.orbit,
            relabelSubgroup e (criticalActionSubgroup i) =
              OrbitProfileFromOrbits.orbitImage H o) :
    HasPositiveSupport H hbinary hresidual ∨ IsEvenCriticalSubgroup N H := by
  rcases hasPositiveSupport_or_allE8 H hbinary hresidual with hsupported | hall
  · exact Or.inl hsupported
  · exact Or.inr
      (isEvenCritical_of_allE8 H hbinary hresidual hall hother)

end SymmetricSubgroupAsymptotics.BinaryDegreeEightCanonicalCarrierProfile

end
