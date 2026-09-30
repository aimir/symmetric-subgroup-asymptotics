import SymmetricSubgroupAsymptotics.BinaryCarrierIndexedKernelReflection
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelEmbedding

/-!
# Kernel-first reflection for reindexed heterogeneous words

This is the word-level wrapper around indexed kernel-first reflection.  The
two routed words may have different occurrence types.  An equivalence of
occurrences, compatible local source and carrier equivalences, and one
commuting faithful ambient square recover the complete correlated source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierIndexedAlignedWordReflection

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierIndexedKernelReflection
open BinaryCarrierKernelNaturalizedReflection
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierWordClosure

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂]
  (slot₁ : ι₁ → Slot) (slot₂ : ι₂ → Slot)

/-- Physical subgroup equality reflects the complete word source even when
the source occurrences themselves must first be reindexed. -/
theorem source_eq_of_physical_subgroup_eq
    (eI : ι₁ ≃ ι₂)
    (chart₁ : WordPointChart slot₁)
    (chart₂ : WordPointChart slot₂)
    (eU : ∀ i, (slot₁ i).Source ≃* (slot₂ (eI i)).Source)
    (eP : ∀ i, carriers slot₁ i ≃* carriers slot₂ (eI i))
    (naturalize : ∀ i,
      (betas slot₁ i).ker.map (eP i).toMonoidHom =
          (betas slot₂ (eI i)).ker →
        QuotientSquare
          (alphas slot₁ i) (alphas slot₂ (eI i))
          (betas slot₁ i) (betas slot₂ (eI i))
          (eU i) (eP i))
    (eD : Equiv.Perm (Fin (2 * wordParameter slot₁)) ≃*
      Equiv.Perm (Fin (2 * wordParameter slot₂)))
    (hembed : eD.toMonoidHom.comp (ambientEmbedding slot₁ chart₁) =
      (ambientEmbedding slot₂ chart₂).comp
        (indexedProductEquiv eI eP).toMonoidHom)
    (H : WordSource slot₁) (K : WordSource slot₂)
    (htarget :
      ((wordPhysicalTargetOn slot₁ chart₁ H).1.map eD.toMonoidHom) =
        (wordPhysicalTargetOn slot₂ chart₂ K).1) :
    H.1.map (indexedProductEquiv eI eU).toMonoidHom = K.1 := by
  apply source_map_eq_of_ambientTransport_map_eq
    eI (alphas slot₁) (alphas slot₂)
    (betas slot₁) (betas slot₂) eU eP H.1 K.1
    H.2.2 K.2.2 (fun i => (slot₂ i).betaSurjective)
    naturalize
    (ambientEmbedding slot₁ chart₁) (ambientEmbedding slot₂ chart₂)
    (ambientEmbedding_injective slot₂ chart₂) eD hembed
  calc
    ((carrierTransport (alphas slot₁) (betas slot₁) H.1).map
        (ambientEmbedding slot₁ chart₁)).map eD.toMonoidHom =
        (wordPhysicalTargetOn slot₁ chart₁ H).1.map eD.toMonoidHom := by
      rw [wordPhysicalTargetOn_subgroup]
    _ = (wordPhysicalTargetOn slot₂ chart₂ K).1 := htarget
    _ = (carrierTransport (alphas slot₂) (betas slot₂) K.1).map
        (ambientEmbedding slot₂ chart₂) :=
      wordPhysicalTargetOn_subgroup slot₂ chart₂ K

end SymmetricSubgroupAsymptotics.BinaryCarrierIndexedAlignedWordReflection

end
