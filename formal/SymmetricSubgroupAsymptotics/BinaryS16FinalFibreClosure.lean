import SymmetricSubgroupAsymptotics.BinaryS16FinalFibreAssembly
import SymmetricSubgroupAsymptotics.BinaryS16DirectDecoderBridge

/-!
# Unconditional closure of the direct S16 target fibre

The native ambient square transports equality of the two physical targets
back through every routed carrier quotient.  The indexed reflection theorem
then recovers the complete correlated word source.  Binary-source reindexing
identifies that result with the canonical flat source, whose faithful original
orbit action recovers the labelled subgroup.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FinalFibreClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierIndexedAlignedWordReflection
open BinaryCarrierIndexedKernelReflection
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierWordClosure
open BinaryS16CommonSourceTransport
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FinalFibreAssembly
open BinaryS16FinalFibrePointAssembly
open BinaryS16FinalFibreReflection
open BinaryS16FixedLiteralNaturality
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

/-- Equality on the fixed original labels is exactly raw-target transport by
the induced native ambient point equivalence. -/
theorem rawTargetSubgroup_map
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    (rawTarget C H).2.1.map
        (wordAmbientPointEquiv (H := H) (K := K) C).permCongrHom.toMonoidHom =
      (rawTarget C K).2.1 := by
  change relabelSubgroup
      (wordAmbientPointEquiv (H := H) (K := K) C) (rawTarget C H).2.1 =
    (rawTarget C K).2.1
  calc
    relabelSubgroup (wordAmbientPointEquiv (H := H) (K := K) C)
        (rawTarget C H).2.1 =
      relabelSubgroup (parameterCast C K).symm
        (relabelSubgroup (parameterCast C H) (rawTarget C H).2.1) := by
      rw [relabelSubgroup_trans, wordAmbientPointEquiv_eq]
    _ = relabelSubgroup (parameterCast C K).symm
        (relabelSubgroup (parameterCast C K) (rawTarget C K).2.1) :=
      congrArg (relabelSubgroup (parameterCast C K).symm) htarget
    _ = (rawTarget C K).2.1 :=
      relabelSubgroup_symm (parameterCast C K) _

/-- The complete routed source word is reflected by the native physical
target subgroup. -/
theorem wordSource_map :
    (wordSource C H).1.map
        (indexedProductEquiv
          (U₁ := fun q => (leftSlot C q).Source)
          (U₂ := fun q => (slot C K q).Source)
          (eI C hblocks htarget)
          (routedSourceEquiv C hblocks htarget)).toMonoidHom =
      (wordSource C K).1 := by
  exact source_eq_of_physical_subgroup_eq
    (slot C H) (slot C K)
    (eI C hblocks htarget)
    (wordPointChart C H) (wordPointChart C K)
    (routedSourceEquiv C hblocks htarget)
    (routedCarrierEquiv C hblocks htarget)
    (routedNaturalizer C hblocks htarget)
    (wordAmbientPointEquiv (H := H) (K := K) C).permCongrHom
    (ambientEmbedding_natural C hblocks htarget)
    (wordSource C H) (wordSource C K)
    (rawTargetSubgroup_map C htarget)

/-- The physical target subgroup reflects the original labelled subgroup on
one fixed-support fibre. -/
theorem subgroup_eq
    (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
      BinaryS16DirectPhysicalEncoding.blocks C K)
    (htarget : targetSubgroup C H = targetSubgroup C K) :
    subgroup C H = subgroup C K := by
  apply (canonicalFlatSource_transport_iff_subgroup_eq
    C hblocks htarget).mp
  exact canonicalFlatSource_eq_of_wordSource_eq C hblocks htarget
    (wordSource_map C hblocks htarget)

end Matched

/-- Full unconditional target-subgroup reflection on every direct S16
fixed-support fibre. -/
theorem reflectsTargetSubgroup : ReflectsTargetSubgroup C := by
  intro H K hblocks htarget
  exact subgroup_eq C hblocks htarget

end SymmetricSubgroupAsymptotics.BinaryS16FinalFibreClosure

end
