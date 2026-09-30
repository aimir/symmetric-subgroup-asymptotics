import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelWordTarget

/-!
# Exact fullness accessors for supplied-chart physical targets

The counted `PhysicalFamily` target intentionally hides its profile witness
behind an existential proposition.  Decoder arguments nevertheless need the
specific supplied chart used by the producer.  These lemmas expose that
fullness directly from the construction, without adding the chart to the
counted target.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelTargetAccessors

open SymmetricSubgroupAsymptotics
open BinaryCarrierOriginalLabelPhysicalTarget
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport

variable {ι : Type*}
  {U Q : ι → Type*} [∀ i, Group (U i)] [∀ i, Group (Q i)]
  {κ : ι → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]

variable
  (C : ∀ i, Subgroup (∀ j, V i j))
  (hC : ∀ i, CarrierProductFull (C i))
  (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
  (hα : ∀ i, Function.Surjective (α i))
  (hβ : ∀ i, Function.Surjective (β i))

variable {R a T : ℕ} (s : ProfileIndex R a T)
  (Dmix : ProfileDisplay (V := V) mixtureAction
    (profileMultiplicity R a T s))

/-- The subgroup constructed by `physicalTargetOn` is full on the exact
supplied chart, not merely on some existentially chosen chart. -/
theorem physicalTargetOn_full {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X)
    (H : CarrierTransportTarget (V := V)) :
    OrbitProfileFullOn mixtureAction e
      (ProfileDisplay.physicalTargetOn s Dmix e H).1 := by
  let M := ProfileDisplay.modelTarget (Ω := mixturePoints)
    mixtureAction (profileMultiplicity R a T s) Dmix H
  have hM : OrbitProfileFullOn mixtureAction (Equiv.refl _) M.1 :=
    (orbitProfileFullOn_iff mixtureAction (Equiv.refl _) M.1).2 M.2
  change OrbitProfileFullOn mixtureAction e (relabelSubgroup e M.1)
  simpa using hM.relabel e

/-- The simultaneous supplied-chart transport inherits the same exact
fullness statement. -/
theorem physicalTransportOn_full {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X)
    [DecidableEq ι] (H : CarrierTransportSource α) :
    OrbitProfileFullOn mixtureAction e
      (physicalTransportOn C hC α β hα hβ s Dmix e H).1 := by
  exact physicalTargetOn_full s Dmix e
    (carrierTransportRecords C hC α β hα hβ H)

/-! ## Numeric casts used by complete words -/

/-- Transporting only the critical-rank index of a physical family does not
change its underlying permutation subgroup. -/
theorem physicalFamily_cast_rank_val
    {X : Type*} {R R' a T : ℕ} (h : R = R')
    (H : PhysicalFamily R a T X) :
    (cast
      (congrArg (fun r ↦ PhysicalFamily r a T X) h) H).1 = H.1 := by
  cases h
  rfl

variable {δ : Type*} [Fintype δ] [DecidableEq δ]
  (slot : δ → BinaryCarrierWordClosure.Slot)

/-- The complete word target remains full on the exact supplied chart after
the producer's purely numerical physical-family cast. -/
theorem wordPhysicalTargetOn_full
    (e : WordPointChart slot)
    (H : BinaryCarrierActualDecoratedProducer.WordSource slot) :
    OrbitProfileFullOn mixtureAction e
      (wordPhysicalTargetOn slot e H).1 := by
  let J := physicalTransportOn
    (C := BinaryCarrierWordClosure.carriers slot)
    (hC := fun i => (slot i).carrierFull)
    (α := BinaryCarrierWordClosure.alphas slot)
    (β := BinaryCarrierWordClosure.betas slot)
    (hα := fun i => (slot i).alphaSurjective)
    (hβ := fun i => (slot i).betaSurjective)
    (s := BinaryCarrierCellProfile.index
      (BinaryCarrierWordClosure.cells slot)
      (BinaryCarrierWordClosure.colors slot))
    (Dmix := BinaryCarrierCellProfile.originalColorDisplay
      (BinaryCarrierWordClosure.cells slot)
      (BinaryCarrierWordClosure.colors slot)) e H
  have hJ : OrbitProfileFullOn mixtureAction e J.1 := by
    exact physicalTransportOn_full
      (C := BinaryCarrierWordClosure.carriers slot)
      (hC := fun i => (slot i).carrierFull)
      (α := BinaryCarrierWordClosure.alphas slot)
      (β := BinaryCarrierWordClosure.betas slot)
      (hα := fun i => (slot i).alphaSurjective)
      (hβ := fun i => (slot i).betaSurjective)
      (s := BinaryCarrierCellProfile.index
        (BinaryCarrierWordClosure.cells slot)
        (BinaryCarrierWordClosure.colors slot))
      (Dmix := BinaryCarrierCellProfile.originalColorDisplay
        (BinaryCarrierWordClosure.cells slot)
        (BinaryCarrierWordClosure.colors slot)) e H
  rw [show (wordPhysicalTargetOn slot e H).1 = J.1 by
    exact physicalFamily_cast_rank_val
      (BinaryCarrierActualDecoratedProducer.wordParameter_sub_wordSupport
        slot).symm J]
  exact hJ

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelTargetAccessors

end
