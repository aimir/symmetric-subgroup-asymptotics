import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceRadical
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
import SymmetricSubgroupAsymptotics.CharacteristicKernelAutomorphismAction
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! The actual source acts on its literal two-coordinate quotient. The
kernel is the proved whole centre, so characteristic-kernel descent has
no ambient linear-group or recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointAction
open CFSG.Models.Chevalley
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleSourceRadical
variable (K : Type) [Field K] [Finite K] [CharP K 3]

private theorem kernel_characteristic : (endpointHom K).ker.Characteristic := by
  rw [←center_eq_endpointKer]
  infer_instance

def endpointAction : Subgroup.normalizer (Middle K : Set (Model CartanMatrix.G₂ K)) →*
    MulAut (Multiplicative (Fin 2 → K)) := by
  letI : (endpointHom K).ker.Characteristic := kernel_characteristic K
  exact (CharacteristicKernelAutomorphismAction.action (endpointHom K)
    (endpointHom_surjective K)).comp (Middle K).normalizerMonoidHom

theorem endpointAction_apply
    (g : Subgroup.normalizer (Middle K : Set (Model CartanMatrix.G₂ K))) (u : Middle K) :
    endpointAction K g (endpointHom K u) =
      endpointHom K ((Middle K).normalizerMonoidHom g u) := by
  letI : (endpointHom K).ker.Characteristic := kernel_characteristic K
  exact CharacteristicKernelAutomorphismAction.automorphism_apply (endpointHom K)
    (endpointHom_surjective K) ((Middle K).normalizerMonoidHom g) u

def toNormalizer : source K →*
    Subgroup.normalizer (Middle K : Set (Model CartanMatrix.G₂ K)) :=
  Subgroup.inclusion (source_le_normalizer_middle K)

def sourceAction : source K →* MulAut (Multiplicative (Fin 2 → K)) :=
  (endpointAction K).comp (toNormalizer K)

def projection : radical K →* Multiplicative (Fin 2 → K) :=
  (endpointHom K).comp (radicalEquiv K).toMonoidHom

theorem projection_surjective : Function.Surjective (projection K) :=
  (endpointHom_surjective K).comp (radicalEquiv K).surjective

theorem sourceAction_apply (p : source K) (u : radical K) :
    letI := radical_normal K
    projection K (MulAut.conjNormal p u) = sourceAction K p (projection K u) := by
  letI := radical_normal K
  have he : radicalEquiv K (MulAut.conjNormal p u) =
      (Middle K).normalizerMonoidHom (toNormalizer K p) (radicalEquiv K u) := by
    apply Subtype.ext
    rfl
  change endpointHom K (radicalEquiv K (MulAut.conjNormal p u)) = _
  rw [he]
  exact (endpointAction_apply K (toNormalizer K p) (radicalEquiv K u)).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleEndpointAction
