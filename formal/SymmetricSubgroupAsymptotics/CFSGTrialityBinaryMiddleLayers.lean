import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingTransport
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleSource
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleVectorAction
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Exact central and quotient layers of the same normal subgroup in
the actual generated source. The quotient conjugation action is the
canonical intrinsic action, with its actual middle-coordinate formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleLayers
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryMiddleNormalizer
open CFSGTrialityBinaryMiddleSource CFSGTrialityBinaryMiddleVectorAction
open CFSGTrialityGeckMiddleCentralExtensionData CFSGTrialityGeckMiddleFixedQuotientCoordinates
open CFSGTrialityGeckMiddleFixedCentralParameters CFSGTrialityBinaryMiddleAutomorphismAction

def layerData (q : CFSG.PrimePower) :
    CentralExtensionScalarPairingIndex.Data (F := F q) (V := fullEnvelope q)
      (N := liftedMiddle q) :=
  CentralExtensionScalarPairingTransport.transport (extensionData q) (middleEquiv q)

theorem layer_projection (q : CFSG.PrimePower) (u : liftedMiddle q) :
    ((layerData q).projection u).toAdd=coordinate q (middleEquiv q u) := rfl

theorem layer_central (q : CFSG.PrimePower) (c : Multiplicative (F q)) :
    ((layerData q).central c).val=middleLift q (central q c) := rfl

def quotientAction (q : CFSG.PrimePower) :
    carrier q →* MulAut (Multiplicative (fullEnvelope q)) :=
  (MulAutMultiplicative (fullEnvelope q)).symm.toMonoidHom.comp
    ((additiveAction q).comp (conjugationAction q))

theorem layer_equivariance (q : CFSG.PrimePower) (g : carrier q) (u : liftedMiddle q) :
    (layerData q).projection (MulAut.conjNormal g u)=
      quotientAction q g ((layerData q).projection u) := by
  have he : middleEquiv q (MulAut.conjNormal g u)=
      conjugationAction q g (middleEquiv q u) := Subtype.ext rfl
  have h := additiveAction_coordinate q (conjugationAction q g) (middleEquiv q u)
  change Multiplicative.ofAdd (coordinate q (middleEquiv q (MulAut.conjNormal g u)))=
    Multiplicative.ofAdd (additiveAction q (conjugationAction q g)
      (coordinate q (middleEquiv q u)))
  rw [he]
  exact congrArg Multiplicative.ofAdd h.symm

theorem quotientAction_toAdd (q : CFSG.PrimePower) (hq : q.order=2)
    (g : carrier q) (v : fullEnvelope q) :
    (quotientAction q g (Multiplicative.ofAdd v)).toAdd=vectorAction q hq g v := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleLayers
