import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates

/-! The actual fixed tensor envelope embeds into the original matrix
coefficient space, consists of genuinely fixed matrices, and spans the whole
cube coefficient space over the cubic extension. Fixedness uses the existing
constructive fixed-word lifts, rather than an assumed lift of quotient fixed
points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedTensorImage

open CFSGTrialityGeckDiagramCovariance CFSGTrialityMiddleFixedTensorSpan
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleFixedLiftSpan CFSGTrialityGeckMiddleLayerCoordinates
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFixedLayer CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckFixedPositiveRaw CFSGSerreOrdinaryTwists

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

def fixedTensorEmbedding (q : CFSG.PrimePower) : fullEnvelope q →ₗ[F q] Mat (K q) :=
  ((tensorCoordinates (K q)).restrictScalars (F q)).comp (fullEnvelope q).subtype

theorem fixedTensorEmbedding_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedTensorEmbedding q) :=
  (tensorCoordinates_injective (K q)).comp Subtype.val_injective

theorem fixedTensorEmbedding_fixed (q : CFSG.PrimePower) (c : fullEnvelope q) :
    matrixTwist (K q) (definingFieldAutomorphism q 3) (fixedTensorEmbedding q c) =
      fixedTensorEmbedding q c := by
  obtain ⟨u, hu⟩ := fixed_fullEnvelope_lifts q c.val c.property
  have hfixed := (mem_fixedPositiveRaw_iff q u.val).mp u.property.2
  have h := fixed_word_firstLayer (K q) (definingFieldAutomorphism q 3) u.val hfixed.2
  change matrixTwist (K q) (definingFieldAutomorphism q 3)
    (tensorCoordinates (K q) c.val) = tensorCoordinates (K q) c.val
  rw [← hu]
  exact h

theorem fixedTensorEmbedding_span (q : CFSG.PrimePower) :
    Submodule.span (K q) (Set.range (fixedTensorEmbedding q)) = cubeSpan (K q) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    rw [← tensorCoordinates_range]
    exact ⟨c.val, rfl⟩
  · have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    rw [← normOrbit_span (K q) q.order hq
      (CFSGTrialityTripleFixedRoots.extension_three_card q)]
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨CFSGCubicNormMonomialSeparation.normCurve q.order t,
      normCurve_mem_fullEnvelope q t⟩, ?_⟩
    exact (normOrbit_coordinates (K q) q.order t).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedTensorImage
