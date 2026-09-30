import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelPhysicalTarget

/-!
# Retained word targets on a supplied original-label chart

The standard heterogeneous-word producer realizes its completed profile on
a canonical `Fin` labelling.  Physical reconstruction already supplies a
canonical chart from the displayed cells to the original ambient labels.
This file inserts that supplied chart into the existing word target while
retaining the same parameter cast and the same retained bin.

The chart is fixed when injectivity is applied.  It is not extra data in the
target and it contributes no counting factor.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelWordTarget

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierCellProfile
open BinaryCarrierOriginalLabelPhysicalTarget
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- A complete chart from the profile displayed by a fixed heterogeneous
word to its original labelled ambient point set. -/
abbrev WordPointChart :=
  OrbitProfilePoints mixturePoints
      (profileMultiplicity
        (criticalRank (cells slot) (colors slot))
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (index (cells slot) (colors slot))) ≃
    Fin (2 * wordParameter slot)

/-- Simultaneous reversible word transport, realized on a supplied complete
original-label chart and then cast through the existing exact critical-rank
identity. -/
def wordPhysicalTargetOn (e : WordPointChart slot) :
    WordSource slot →
      PhysicalFamily
        (wordParameter slot - wordSupport slot)
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (Fin (2 * wordParameter slot)) := fun H =>
  cast (wordFamilyType_eq slot)
    (physicalTransportOn
      (C := carriers slot)
      (hC := fun i => (slot i).carrierFull)
      (α := alphas slot)
      (β := betas slot)
      (hα := fun i => (slot i).alphaSurjective)
      (hβ := fun i => (slot i).betaSurjective)
      (s := index (cells slot) (colors slot))
      (Dmix := originalColorDisplay (cells slot) (colors slot)) e H)

/-- A fixed supplied point chart loses no word source. -/
theorem wordPhysicalTargetOn_injective (e : WordPointChart slot) :
    Function.Injective (wordPhysicalTargetOn slot e) :=
  (cast_bijective (wordFamilyType_eq slot)).injective.comp
    (physicalTransportOn_injective
      (C := carriers slot)
      (hC := fun i => (slot i).carrierFull)
      (α := alphas slot)
      (β := betas slot)
      (hα := fun i => (slot i).alphaSurjective)
      (hβ := fun i => (slot i).betaSurjective)
      (s := index (cells slot) (colors slot))
      (Dmix := originalColorDisplay (cells slot) (colors slot)) e)

/-- Insert the supplied-chart physical word into the same canonical retained
bin used by the standard word target. -/
def wordTargetOn (e : WordPointChart slot) {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i,
      ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    WordSource slot → Target (wordParameter slot) Cold := fun H =>
  ⟨retainedWordBin slot hnoncritical R, wordPhysicalTargetOn slot e H⟩

/-- Retained-bin insertion preserves the injectivity of the complete
supplied-chart word transport. -/
theorem wordTargetOn_injective (e : WordPointChart slot) {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i,
      ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    Function.Injective (wordTargetOn slot e hnoncritical R) := by
  intro H H' h
  apply wordPhysicalTargetOn_injective slot e
  exact (@sigma_mk_injective
    (RetainedBin (wordParameter slot) Cold)
    (fun b ↦ PhysicalFamily
      (wordParameter slot - binSupport b.1)
      b.1.1.1 b.1.1.2 (Fin (2 * wordParameter slot)))
    (retainedWordBin slot hnoncritical R)) h

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelWordTarget

end
