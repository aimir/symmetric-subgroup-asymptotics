import SymmetricSubgroupAsymptotics.CharacteristicKernelAutomorphismAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointCentralKernel
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplement

/-! The actual normalizer acts on the two-endpoint quotient of the same
fixed middle radical. Characteristic-kernel descent is discharged by the
proved equality with the full centre. The actual short Weyl word is a
member of this normalizer, with no abstract Levi identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointNormalizerAction

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckShortComplement
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleEndpointProjection
open CFSGGTwoD4GeckMiddleEndpointCentralKernel
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

variable (K : Type) [Field K] [Finite K] [CharP K 3]

private theorem kernel_characteristic (hcard : 4 ≤ Nat.card K) :
    (endpointHom K).ker.Characteristic := by
  change (endpointKernel K).Characteristic
  rw [←center_eq_endpointKernel K hcard]
  infer_instance

def endpointAction (hcard : 4 ≤ Nat.card K) :
    Subgroup.normalizer (fixedMiddle K : Set (Raw K)) →*
      MulAut (Multiplicative (Fin 2 → K)) := by
  letI : (endpointHom K).ker.Characteristic := kernel_characteristic K hcard
  exact (CharacteristicKernelAutomorphismAction.action (endpointHom K)
    (endpointHom_surjective K hcard)).comp (fixedMiddle K).normalizerMonoidHom

theorem endpointAction_apply (hcard : 4 ≤ Nat.card K)
    (g : Subgroup.normalizer (fixedMiddle K : Set (Raw K))) (u : fixedMiddle K) :
    endpointAction K hcard g (endpointHom K u) =
      endpointHom K ((fixedMiddle K).normalizerMonoidHom g u) := by
  letI : (endpointHom K).ker.Characteristic := kernel_characteristic K hcard
  exact CharacteristicKernelAutomorphismAction.automorphism_apply (endpointHom K)
    (endpointHom_surjective K hcard) ((fixedMiddle K).normalizerMonoidHom g) u

theorem shortWeyl_normalizes_fixedMiddle :
    shortWeyl K ∈ Subgroup.normalizer (fixedMiddle K : Set (Raw K)) := by
  have hn : shortWeyl K ∈ Subgroup.normalizer (middleRadical K : Set (Raw K)) := by
    rw [middleRadical_eq_shortComplement]
    exact shortWeyl_mem_normalizer_shortComplement K
  exact CFSGFixedSubgroupConjugation.normalizes_inf_fixed
    (unitTwist K (RingEquiv.refl K)) (middleRadical K) (shortWeyl K)
    (shortWeyl_fixed K (RingEquiv.refl K)) hn

def shortWeylElement : Subgroup.normalizer (fixedMiddle K : Set (Raw K)) :=
  ⟨shortWeyl K,shortWeyl_normalizes_fixedMiddle K⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointNormalizerAction
