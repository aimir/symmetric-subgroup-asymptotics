import SymmetricSubgroupAsymptotics.BinaryS16FinalFibrePointAssembly

/-!
# Ambient embedding assembly for the direct S16 fibre reflection

The native literal point square is already compiled in the imported module.
This module combines it with local carrier-action naturality and exposes the
single ambient embedding square used by indexed source reflection.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16FinalFibreAssembly

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierFusionEmbeddingFormula
open BinaryCarrierIndexedKernelReflection
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierWordClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FinalFibreReflection
open BinaryS16FinalFibrePointAssembly
open BinaryS16FixedLiteralNaturality
open BinaryS16FusionNaturalPointChart

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)
abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

section Matched

variable {H K : Actual C}
variable (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
  BinaryS16DirectPhysicalEncoding.blocks C K)
variable (htarget : targetSubgroup C H = targetSubgroup C K)

/-- The two faithful raw ambient embeddings commute with simultaneous
carrier transport. -/
theorem ambientEmbedding_natural :
    (wordAmbientPointEquiv (H := H) (K := K) C).permCongrHom.toMonoidHom.comp
        (ambientEmbedding (slot C H) (wordPointChart C H)) =
      (ambientEmbedding (slot C K) (wordPointChart C K)).comp
        (indexedProductEquiv
          (U₁ := fun q => carriers (slot C H) q)
          (U₂ := fun q => carriers (slot C K) q)
          (eI C hblocks htarget)
          (routedCarrierEquiv C hblocks htarget)).toMonoidHom := by
  let d := (wordAmbientPointEquiv (H := H) (K := K) C).permCongrHom.toMonoidHom
  let lH := (wordLiteralPointChart C H).permCongrHom.toMonoidHom
  let lK := (wordLiteralPointChart C K).permCongrHom.toMonoidHom
  let r := (routedLiteralPointEquiv C hblocks htarget).permCongrHom.toMonoidHom
  let aH := literalAction (slot C H)
  let aK := literalAction (slot C K)
  let eP := (indexedProductEquiv
    (U₁ := fun q => carriers (slot C H) q)
    (U₂ := fun q => carriers (slot C K) q)
    (eI C hblocks htarget)
    (routedCarrierEquiv C hblocks htarget)).toMonoidHom
  have hambH : ambientEmbedding (slot C H) (wordPointChart C H) =
      lH.comp aH := ambientEmbedding_wordPointChart C H
  have hambK : ambientEmbedding (slot C K) (wordPointChart C K) =
      lK.comp aK := ambientEmbedding_wordPointChart C K
  have hpoint : d.comp lH = lK.comp r :=
    permCongrHom_comp_of_trans_eq
      (wordLiteralPointChart C H) (wordLiteralPointChart C K)
      (routedLiteralPointEquiv C hblocks htarget)
      (wordAmbientPointEquiv (H := H) (K := K) C)
      (wordLiteralPointChart_natural C hblocks htarget)
  have haction : r.comp aH = aK.comp eP := by
    apply MonoidHom.ext
    intro p
    exact literalAction_natural C hblocks htarget p
  calc
    d.comp (ambientEmbedding (slot C H) (wordPointChart C H)) =
        d.comp (lH.comp aH) := congrArg d.comp hambH
    _ = (d.comp lH).comp aH := rfl
    _ = (lK.comp r).comp aH := congrArg (fun f => f.comp aH) hpoint
    _ = lK.comp (r.comp aH) := rfl
    _ = lK.comp (aK.comp eP) := congrArg (lK.comp) haction
    _ = (lK.comp aK).comp eP := rfl
    _ = (ambientEmbedding (slot C K) (wordPointChart C K)).comp eP :=
      congrArg (fun f => f.comp eP) hambK.symm

end Matched

end SymmetricSubgroupAsymptotics.BinaryS16FinalFibreAssembly

end
