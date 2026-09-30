import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding

/-!
# Factorization of the retained word target through its fixed profile display

The canonical word target first performs simultaneous carrier transport,
then applies the fixed original-colour display and physical relabelling, and
finally inserts the result into its retained parameter bin.  This file makes
that definitional factorization explicit so the mixed incidence argument can
reuse fixed-chart injectivity without unfolding the complete producer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWordTargetFactorization

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCellProfile
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- For one fixed heterogeneous word, realize a literal full displayed
ambient subgroup in the word's retained physical bin. -/
def fixedWordPhysicalizer {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i,
      ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    CarrierTransportTarget
        (V := fun i j => mixtureAction (colors slot ⟨i,j⟩)) →
      BinaryCarrierActualDecoratedTransport.Target
        (wordParameter slot) Cold := fun J =>
  retainedBinTarget (retainedWordBin slot hnoncritical R)
    (cast (wordFamilyType_eq slot)
      ((originalColorDisplay (cells slot) (colors slot)).physicalTarget
        (index (cells slot) (colors slot)) J))

/-- Faithfulness of the fixed display, its point relabelling, the harmless
type cast, and retained-bin insertion makes the complete physicalizer
injective. -/
theorem fixedWordPhysicalizer_injective {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i,
      ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    Function.Injective (fixedWordPhysicalizer slot hnoncritical R) := by
  apply (retainedBinTarget_injective
    (retainedWordBin slot hnoncritical R)).comp
  apply (cast_bijective (wordFamilyType_eq slot)).injective.comp
  exact ProfileDisplay.physicalTarget_injective
    (s := index (cells slot) (colors slot))
    (Dmix := originalColorDisplay (cells slot) (colors slot))

/-- The actual retained-bin word target factors through the literal
simultaneous carrier subgroup and its fixed original-colour display. -/
theorem wordTarget_eq_retainedBin_physicalTarget {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i,
      ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold)
    (H : WordSource slot) :
    wordTarget slot hnoncritical R H =
      fixedWordPhysicalizer slot hnoncritical R
        (carrierTransportRecords
          (carriers slot)
          (fun i => (slot i).carrierFull)
          (alphas slot) (betas slot)
          (fun i => (slot i).alphaSurjective)
          (fun i => (slot i).betaSurjective) H) := by
  have hphysical := physicalTransport_eq_physicalTarget
    (C := carriers slot)
    (hC := fun i => (slot i).carrierFull)
    (α := alphas slot)
    (β := betas slot)
    (hα := fun i => (slot i).alphaSurjective)
    (hβ := fun i => (slot i).betaSurjective)
    (s := index (cells slot) (colors slot))
    (Dmix := originalColorDisplay (cells slot) (colors slot)) H
  have hcast := congrArg (fun z => cast (wordFamilyType_eq slot) z) hphysical
  unfold wordTarget fixedWordPhysicalizer retainedBinTarget wordPhysicalTarget
  congr 1

end SymmetricSubgroupAsymptotics.BinaryCarrierWordTargetFactorization
