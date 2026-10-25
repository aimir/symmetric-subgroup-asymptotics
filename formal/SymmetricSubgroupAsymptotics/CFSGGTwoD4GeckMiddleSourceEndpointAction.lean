import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceNormalizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFullCentralLine
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Honest endpoint data on the actual source normalizer intersection.
The normal radical is equivalent to the same fixed middle group, and
both the full central embedding and quotient action use that equivalence.
No complement, automorphism lift or new recognition premise is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceEndpointAction
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleSourceNormalizer
open CFSGGTwoD4GeckMiddleEndpointProjection CFSGGTwoD4GeckMiddleEndpointNormalizerAction
open CFSGGTwoD4GeckMiddleEndpointCentralKernel CFSGGTwoD4GeckMiddleFullCentralLine
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def toAmbientNormalizer : sourceNormalizer K →*
    Subgroup.normalizer (fixedMiddle K : Set (Raw K)) := Subgroup.inclusion inf_le_left

def sourceAction (hcard : 4 ≤ Nat.card K) :
    sourceNormalizer K →* MulAut (Multiplicative (Fin 2 → K)) :=
  (endpointAction K hcard).comp (toAmbientNormalizer K)

def projection : radical K →* Multiplicative (Fin 2 → K) :=
  (endpointHom K).comp (radicalEquiv K).toMonoidHom

theorem projection_surjective (hcard : 4 ≤ Nat.card K) :
    Function.Surjective (projection K) :=
  (endpointHom_surjective K hcard).comp (radicalEquiv K).surjective

theorem sourceAction_apply (hcard : 4 ≤ Nat.card K) (p : sourceNormalizer K) (u : radical K) :
    projection K (MulAut.conjNormal p u) = sourceAction K hcard p (projection K u) := by
  have he : radicalEquiv K (MulAut.conjNormal p u) =
      (fixedMiddle K).normalizerMonoidHom (toAmbientNormalizer K p) (radicalEquiv K u) := by
    apply Subtype.ext
    rfl
  change endpointHom K (radicalEquiv K (MulAut.conjNormal p u)) = _
  rw [he]
  exact (endpointAction_apply K hcard (toAmbientNormalizer K p) (radicalEquiv K u)).symm

def centralEmbedding : Subgroup.center (fixedMiddle K) →* radical K :=
  (radicalEquiv K).symm.toMonoidHom.comp (Subgroup.center (fixedMiddle K)).subtype

theorem centralEmbedding_injective : Function.Injective (centralEmbedding K) :=
  (radicalEquiv K).symm.injective.comp Subtype.val_injective

theorem centralEmbedding_range (hcard : 4 ≤ Nat.card K) :
    (centralEmbedding K).range = (projection K).ker := by
  ext u
  constructor
  · rintro ⟨z,rfl⟩
    change endpointHom K (radicalEquiv K ((radicalEquiv K).symm z.val)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact (center_subtype_range K hcard).le ⟨z,rfl⟩
  · intro hu
    have he : radicalEquiv K u ∈ Subgroup.center (fixedMiddle K) := by
      rw [center_eq_endpointKernel K hcard]
      exact hu
    exact ⟨⟨radicalEquiv K u,he⟩,(radicalEquiv K).symm_apply_apply u⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceEndpointAction
