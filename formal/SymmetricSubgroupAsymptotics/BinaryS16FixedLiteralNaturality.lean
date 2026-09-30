import SymmetricSubgroupAsymptotics.BinaryS16FinalFibreReflection

/-!
# Fixed-label literal naturality for the direct S16 fibre

This module keeps the last numerical point casts separate from the finite
route analysis.  The imported module proves local naturality for every
quotient-identity and proper carrier cell and reconstructs the correlated
flat source.  Here those cells are assembled on the native word degree, the
two exact half-degree casts are cancelled, and the indexed word theorem is
applied.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FixedLiteralNaturality

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierFusionEmbeddingFormula
open BinaryCarrierIndexedAlignedWordReflection
open BinaryCarrierIndexedKernelReflection
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierWordClosure
open BinaryS16CommonSourceTransport
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FinalFibreReflection
open BinaryS16FusionNaturalPointChart
open BinaryS16JointOrbitData
open BinaryS16SourceOrbitReindex

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

section Matched

variable {H K : Actual C}
variable (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
  BinaryS16DirectPhysicalEncoding.blocks C K)
variable (htarget : targetSubgroup C H = targetSubgroup C K)

/-- Cast the routed word's native half-degree to the fixed ambient
half-degree. -/
abbrev parameterCast (L : Actual C) :
    Fin (2 * wordParameter (slot C L)) ≃ Fin (2 * N) :=
  wordParameterCast C L

/-- The raw ambient point equivalence forced by the two exact parameter
identities. -/
def wordAmbientPointEquiv :
    Fin (2 * wordParameter (slot C H)) ≃
      Fin (2 * wordParameter (slot C K)) :=
  (parameterCast C H).trans (parameterCast C K).symm

/-- Literal displayed points assembled on the fixed original ambient labels. -/
abbrev fixedLiteralPointChart (L : Actual C) :=
  BinaryS16DirectPhysicalTarget.fixedLiteralPointChart C L

/-- Reindexing displayed occurrences does not change their original ambient
labels. -/
theorem fixedLiteralPointChart_natural :
    (routedLiteralPointEquiv C hblocks htarget).trans
        (fixedLiteralPointChart C K) =
      fixedLiteralPointChart C H := by
  apply Equiv.ext
  rintro ⟨q,z⟩
  have hsigma :
      occurrencePointEquiv C hblocks htarget
          ⟨q,slotChart (subgroup C H) (residualSector C H) q z⟩ =
        ⟨eI C hblocks htarget q,
          slotChart (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q)
            (routedDisplayedPointEquiv C hblocks htarget q z)⟩ := by
    change
      (⟨eI C hblocks htarget q,
        occurrenceLocalPointEquiv C hblocks htarget q
          (slotChart (subgroup C H) (residualSector C H) q z)⟩ :
        Σ r : Occurrence C K,
          Points (subgroup C K) (residualSector C K) r.1) = _
    exact Sigma.ext rfl (heq_of_eq (by
      simp [routedDisplayedPointEquiv]))
  calc
    fixedLiteralPointChart C K
        (routedLiteralPointEquiv C hblocks htarget ⟨q,z⟩) =
      assemble (subgroup C K) (residualSector C K)
        ⟨eI C hblocks htarget q,
          slotChart (subgroup C K) (residualSector C K)
            (eI C hblocks htarget q)
            (routedDisplayedPointEquiv C hblocks htarget q z)⟩ := rfl
    _ = assemble (subgroup C K) (residualSector C K)
        (occurrencePointEquiv C hblocks htarget
          ⟨q,slotChart (subgroup C H) (residualSector C H) q z⟩) := by
      rw [hsigma]
    _ = assemble (subgroup C H) (residualSector C H)
        ⟨q,slotChart (subgroup C H) (residualSector C H) q z⟩ :=
      assemble_occurrencePointEquiv C hblocks htarget
        ⟨q,slotChart (subgroup C H) (residualSector C H) q z⟩
    _ = fixedLiteralPointChart C H ⟨q,z⟩ := rfl

end Matched

end SymmetricSubgroupAsymptotics.BinaryS16FixedLiteralNaturality

end
