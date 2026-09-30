import SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitPartition
import SymmetricSubgroupAsymptotics.BinaryS16FusionNaturalPointChart

/-!
# Reindexing the joint S16 profile along the literal source-orbit matching

Equality of the two physical keys gives an equivalence between the source
orbit quotients which preserves the underlying subsets of the original
labelled point set.  This file lifts that equivalence through the singleton
occurrence presentation used by `BinaryS16JointOrbitData`.

The important point is that this lift does not compare arbitrary choices of
orbit representatives.  On every matched occurrence it uses the two exact
local charts and the equality of their literal orbit sets.  Consequently the
resulting point equivalence commutes with the two simultaneous assembly
charts on the nose after forgetting subtype proofs.

This is the source-orbit part of the final decoder.  Route-slot naturality is
deliberately kept separate: recorded routes must be transported using the
matched mixed record, while the five omitted constructors use their one-cell
identity routes.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitReindex

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierFusionNaturalPointChart
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16JointOrbitData
open BinaryS16SourceOrbitPartition

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- The occurrence type of the direct joint orbit profile. -/
abbrev Occurrence (H : Actual C) :=
  Σ o, Fin ((data (subgroup C H) (residualSector C H)).multiplicity o)

/-- Reindex joint-profile occurrences through the unique matching literal
source orbit.  Writing this with the two `orbitIndex` equivalences avoids any
dependence on the implementation of the singleton occurrence enumeration. -/
def occurrenceEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    Occurrence C H ≃ Occurrence C K :=
  (data (subgroup C H) (residualSector C H)).orbitIndex |>.trans
    ((sourceOrbitEquiv C hblocks htarget).trans
      (data (subgroup C K) (residualSector C K)).orbitIndex.symm)

@[simp] theorem occurrenceEquiv_orbitIndex
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) :
    (data (subgroup C K) (residualSector C K)).orbitIndex
        (occurrenceEquiv C hblocks htarget q) =
      (sourceOrbitEquiv C hblocks htarget)
        ((data (subgroup C H) (residualSector C H)).orbitIndex q) := by
  simp only [occurrenceEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

@[simp] theorem occurrenceEquiv_fst
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) :
    (occurrenceEquiv C hblocks htarget q).1 =
      (sourceOrbitEquiv C hblocks htarget) q.1 := by
  calc
    (occurrenceEquiv C hblocks htarget q).1 =
        (data (subgroup C K) (residualSector C K)).orbitIndex
          (occurrenceEquiv C hblocks htarget q) :=
      (orbitIndex_eq_fst (subgroup C K) (residualSector C K)
        (occurrenceEquiv C hblocks htarget q)).symm
    _ = (sourceOrbitEquiv C hblocks htarget)
        ((data (subgroup C H) (residualSector C H)).orbitIndex q) :=
      occurrenceEquiv_orbitIndex C hblocks htarget q
    _ = (sourceOrbitEquiv C hblocks htarget) q.1 := by
      rw [orbitIndex_eq_fst]

/-- The matched occurrences index literally the same subset of the ambient
point set.  This is the equality used to move between their exact local
charts. -/
theorem occurrenceEquiv_orbit
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) :
    ((data (subgroup C K) (residualSector C K)).orbitIndex
        (occurrenceEquiv C hblocks htarget q)).orbit =
      ((data (subgroup C H) (residualSector C H)).orbitIndex q).orbit := by
  rw [occurrenceEquiv_orbitIndex]
  exact sourceOrbitEquiv_orbit C hblocks htarget
    ((data (subgroup C H) (residualSector C H)).orbitIndex q)

/-- The exact local point equivalence over a matched occurrence.  It first
uses the left local chart, then regards the resulting labelled point as an
element of the equal right orbit set, and finally returns through the right
local chart. -/
def occurrenceLocalPointEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H) :
    Points (subgroup C H) (residualSector C H) q.1 ≃
      Points (subgroup C K) (residualSector C K)
        (occurrenceEquiv C hblocks htarget q).1 :=
  ((data (subgroup C H) (residualSector C H)).localChart q.1 q.2).trans
    ((Equiv.setCongr
        (occurrenceEquiv_orbit C hblocks htarget q).symm).trans
      ((data (subgroup C K) (residualSector C K)).localChart
        (occurrenceEquiv C hblocks htarget q).1
        (occurrenceEquiv C hblocks htarget q).2).symm)

/-- The local point equivalence preserves the original ambient label. -/
@[simp] theorem occurrenceLocalPointEquiv_chart
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (q : Occurrence C H)
    (x : Points (subgroup C H) (residualSector C H) q.1) :
    (((data (subgroup C K) (residualSector C K)).localChart
        (occurrenceEquiv C hblocks htarget q).1
        (occurrenceEquiv C hblocks htarget q).2
        (occurrenceLocalPointEquiv C hblocks htarget q x) :
          ((data (subgroup C K) (residualSector C K)).orbitIndex
            (occurrenceEquiv C hblocks htarget q)).orbit) : Fin (2 * N)) =
      (((data (subgroup C H) (residualSector C H)).localChart q.1 q.2 x :
          ((data (subgroup C H) (residualSector C H)).orbitIndex q).orbit) :
        Fin (2 * N)) := by
  simp only [occurrenceLocalPointEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

/-- Reindex the complete sigma of occurrence points.  Unlike a bare
cardinality equivalence, this remembers exactly which literal source block
each point belongs to. -/
def occurrencePointEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    (Σ q : Occurrence C H,
      Points (subgroup C H) (residualSector C H) q.1) ≃
    (Σ q : Occurrence C K,
      Points (subgroup C K) (residualSector C K) q.1) :=
  Equiv.sigmaCongr (occurrenceEquiv C hblocks htarget)
    (occurrenceLocalPointEquiv C hblocks htarget)

@[simp] theorem occurrencePointEquiv_fst
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (z : Σ q : Occurrence C H,
      Points (subgroup C H) (residualSector C H) q.1) :
    (occurrencePointEquiv C hblocks htarget z).1 =
      occurrenceEquiv C hblocks htarget z.1 := rfl

/-- Reindex the complete profile point type by first separating an occurrence
from its local point, applying the literal occurrence-point equivalence, and
regrouping the result. -/
def profilePointEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    OrbitProfilePoints
        (Points (subgroup C H) (residualSector C H))
        (data (subgroup C H) (residualSector C H)).multiplicity ≃
      OrbitProfilePoints
        (Points (subgroup C K) (residualSector C K))
        (data (subgroup C K) (residualSector C K)).multiplicity :=
  (profilePointEquivOccurrencePoint
      (Points (subgroup C H) (residualSector C H))
      (data (subgroup C H) (residualSector C H)).multiplicity).trans
    ((occurrencePointEquiv C hblocks htarget).trans
      (profilePointEquivOccurrencePoint
        (Points (subgroup C K) (residualSector C K))
        (data (subgroup C K) (residualSector C K)).multiplicity).symm)

/-- The reindexed complete joint profile has exactly the same simultaneous
chart into the original labelled ambient set. -/
theorem profilePointEquiv_chart
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (z : OrbitProfilePoints
      (Points (subgroup C H) (residualSector C H))
      (data (subgroup C H) (residualSector C H)).multiplicity) :
    (data (subgroup C K) (residualSector C K)).chart
        (profilePointEquiv C hblocks htarget z) =
      (data (subgroup C H) (residualSector C H)).chart z := by
  rcases z with ⟨o,j,x⟩
  simp only [profilePointEquiv, Equiv.trans_apply,
    profilePointEquivOccurrencePoint, occurrencePointEquiv,
    Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  rw [OrbitProfileFromOrbits.Data.chart_apply,
    OrbitProfileFromOrbits.Data.chart_apply]
  exact occurrenceLocalPointEquiv_chart C hblocks htarget ⟨o,j⟩ x

/-- Occurrence-point form of the same statement, phrased with the assembly
equivalences used by the fusion-natural S16 point chart. -/
theorem assemble_occurrencePointEquiv
    {H K : Actual C}
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K)
    (z : Σ q : Occurrence C H,
      Points (subgroup C H) (residualSector C H) q.1) :
    BinaryS16FusionNaturalPointChart.assemble
        (subgroup C K) (residualSector C K)
        (occurrencePointEquiv C hblocks htarget z) =
      BinaryS16FusionNaturalPointChart.assemble
        (subgroup C H) (residualSector C H) z := by
  exact profilePointEquiv_chart C hblocks htarget
    ((profilePointEquivOccurrencePoint
      (Points (subgroup C H) (residualSector C H))
      (data (subgroup C H) (residualSector C H)).multiplicity).symm z)

end SymmetricSubgroupAsymptotics.BinaryS16SourceOrbitReindex

end
