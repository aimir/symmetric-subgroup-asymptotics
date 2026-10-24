import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleScalarPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedTensorImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleAllCommutators

/-! The scalar pairing on genuine fixed first coefficients is valued in
the literal fixed field. Actual fixed-word lifts supply the two radical
elements, their actual commutator supplies a fixed highest-root parameter,
and the generic degree-two identity identifies precisely that parameter.
There is no averaging or fixed-quotient lifting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedPairingValues

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityMiddleFixedTensorSpan
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleFixedLiftSpan
open CFSGTrialityGeckMiddleFixedTensorImage CFSGTrialityGeckMiddleAllCommutators
open CFSGTrialityGeckMiddleScalarPairing CFSGTrialityGeckMiddleHighestSecondLayer
open CFSGGradedMatrixCommutatorSecondLayer CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixGroupFirstLayer CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootBracketTransport CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open scoped commutatorElement

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def fixedCubeEmbedding (q : CFSG.PrimePower) : fullEnvelope q →ₗ[F q] cubeSpan (K q) :=
  (fixedTensorEmbedding q).codRestrict ((cubeSpan (K q)).restrictScalars (F q)) (fun c => by
    change fixedTensorEmbedding q c ∈ cubeSpan (K q)
    rw [← fixedTensorEmbedding_span]
    exact Submodule.subset_span (Set.mem_range_self c))

theorem fixedCubeEmbedding_val (q : CFSG.PrimePower) (c : fullEnvelope q) :
    (fixedCubeEmbedding q c).val = tensorCoordinates (K q) c.val := rfl

theorem fixedCubeEmbedding_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedCubeEmbedding q) := by
  intro c d he
  apply fixedTensorEmbedding_injective q
  exact congrArg Subtype.val he

theorem fixed_middle_pairing_parameter (q : CFSG.PrimePower) (u v : fixedMiddle q)
    (c d : fullEnvelope q)
    (hu : firstLayer middleWeight u.val = tensorCoordinates (K q) c.val)
    (hv : firstLayer middleWeight v.val = tensorCoordinates (K q) d.val) :
    ∃ t : fixedField q,
      selectedRootElement A hd hs hp ho (K q) (longRoot 2) t.val = ⁅u.val, v.val⁆ ∧
      cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d) = t.val := by
  obtain ⟨t, ht⟩ := fixed_middle_commutator_parameter q u v
  refine ⟨t, ht, ?_⟩
  let r : Raw (K q) := u.val
  let s : Raw (K q) := v.val
  have hr := middle_le_strict (K q) u.property.1
  have hspos := middle_le_strict (K q) v.property.1
  have h2 := commutator_secondLayer middleWeight r s hr hspos
  let P : Raw (K q) → Mat (K q) := fun z => degreePart middleWeight (2 : ℤ)
    ((z.val : Mat (K q)) - (1 : Mat (K q)))
  have hproject : P (r * s * r⁻¹ * s⁻¹) =
      P (selectedRootElement A hd hs hp ho (K q) (longRoot 2) t.val) := by
    simpa only [commutatorElement_def] using congrArg P ht.symm
  have htop : P (selectedRootElement A hd hs hp ho (K q) (longRoot 2) t.val) =
      t.val • selectedFieldCoefficient A hd hs hp ho (K q) (longRoot 2) :=
    highest_secondLayer (K q) t.val
  have hbr := h2.symm.trans (hproject.trans htop)
  have he : ⁅tensorCoordinates (K q) c.val, tensorCoordinates (K q) d.val⁆ =
      t.val • selectedFieldCoefficient A hd hs hp ho (K q) (longRoot 2) :=
    (congrArg₂ (fun M N : Mat (K q) => ⁅M, N⁆) hu hv).symm.trans hbr
  change highestFunctional (K q)
    ⁅tensorCoordinates (K q) c.val, tensorCoordinates (K q) d.val⁆ = t.val
  rw [he]
  let E : Mat (K q) := selectedFieldCoefficient A hd hs hp ho (K q) (longRoot 2)
  have hlinear := (highestFunctional (K q)).map_smul (t.val : K q) E
  have hvalue : highestFunctional (K q) E = 1 := highestFunctional_highest (K q)
  exact hlinear.trans
    ((congrArg (fun z : K q => t.val * z) hvalue).trans (mul_one t.val))

theorem pairing_fixed_field (q : CFSG.PrimePower) (c d : fullEnvelope q) :
    definingFieldAutomorphism q 3
      (cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d)) =
      cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d) := by
  obtain ⟨u, hu⟩ := fixed_fullEnvelope_lifts q c.val c.property
  obtain ⟨v, hv⟩ := fixed_fullEnvelope_lifts q d.val d.property
  obtain ⟨t, _, ht⟩ := fixed_middle_pairing_parameter q u v c d hu hv
  rw [ht]
  exact t.property

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedPairingValues
