import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEquiv
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLayer
import SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorSpan

/-! Coordinates of the actual first layer of every radical word. A fixed
word has coordinates in the genuine eight-dimensional base-field tensor
envelope. This is only an inclusion: fixed quotient lifting is neither
assumed nor inferred. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubeEquiv
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleFixedLayer CFSGTrialityGeckMatrixTwist
open CFSGTrialityMiddleFixedTensorSpan CFSGCubicTensorEnvelopeDimension
open CFSGGradedMatrixGroupFirstLayer CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem tensorCoordinates_range (K : Type) [Field K] :
    (tensorCoordinates K).range = cubeSpan K := by
  have h := Fintype.range_linearCombination K (actualTensor K)
  change (tensorCoordinates K).range = Submodule.span K (Set.range (actualTensor K)) at h
  rw [h]
  have hrange : Set.range (actualTensor K) = Set.range (tensorBasis K) := by
    ext M
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cubeBits i, (tensorWord_eq K i).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨i, rfl⟩ := cubeBits_bijective.2 a
      exact ⟨i, tensorWord_eq K i⟩
  rw [hrange, span_tensorBasis_eq]

theorem firstLayer_mem_cubeSpan (K : Type) [Field K] [Finite K]
    (u : middleRadical K) : firstLayer middleWeight u.val ∈ cubeSpan K := by
  obtain ⟨c, hc⟩ := cubeProduct_surjective K (QuotientGroup.mk' (highestInMiddle K) u)
  have he := congrArg (fun z : MiddleQuotient K => (quotientFirstLayerHom K z).toAdd) hc
  dsimp only at he
  rw [cubeProduct_firstLayer] at he
  change (∑ a, (c a).toAdd • cubeCoefficient K a) = firstLayer middleWeight u.val at he
  rw [← he]
  apply Submodule.sum_mem
  intro a _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

theorem exists_firstLayer_coordinates (K : Type) [Field K] [Finite K]
    (u : middleRadical K) :
    ∃ c : Fin 8 → K, tensorCoordinates K c = firstLayer middleWeight u.val := by
  have hm := firstLayer_mem_cubeSpan K u
  rw [← tensorCoordinates_range] at hm
  exact hm

theorem exists_fixed_firstLayer_coordinates (q : CFSG.PrimePower)
    (u : middleRadical (q.Extension 3))
    (hu : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) u.val = u.val) :
    ∃ c : Fin 8 → q.Extension 3, c ∈ fullEnvelope q ∧
      tensorCoordinates (q.Extension 3) c = firstLayer middleWeight u.val := by
  obtain ⟨c, hc⟩ := exists_firstLayer_coordinates (q.Extension 3) u
  have hfixed : matrixTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (tensorCoordinates (q.Extension 3) c) = tensorCoordinates (q.Extension 3) c := by
    rw [hc, fixed_word_firstLayer _ _ _ hu]
  obtain ⟨h0,h7,h2,h4,h6,h5⟩ := fixed_tensorCoordinate_conditions
    (q.Extension 3) (definingFieldAutomorphism q 3) c hfixed
  refine ⟨c, ?_, hc⟩
  exact mem_tensorEnvelope _ _ _ ((mem_fixedScalarSpace q _).mpr h0)
    ((mem_fixedScalarSpace q _).mpr h7) h2 h4 h6 h5

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates
