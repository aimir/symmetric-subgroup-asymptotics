import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeComponentChart
import SymmetricSubgroupAsymptotics.ModuleUniformProjectorSharing

/-! The projector is an actual element of the retained S4 group algebra. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

def envelopeCycleElement : SymmetricComplement :=
  envelopeTernaryInclusion (Multiplicative.ofAdd 1)

def envelopeTraceAlgebra : Scalar[SymmetricComplement] :=
  MonoidAlgebra.single 1 1 + MonoidAlgebra.single envelopeCycleElement 1 +
    MonoidAlgebra.single (envelopeCycleElement ^ 2) 1

def envelopeTraceOperator : _root_.Module.End Scalar SymmetricEnvelope :=
  symmetricEnvelopeRepresentation 1 + symmetricEnvelopeRepresentation envelopeCycleElement +
    symmetricEnvelopeRepresentation (envelopeCycleElement ^ 2)

theorem envelopeTraceOperator_eq : envelopeTraceOperator =
    symmetricEnvelopeRepresentation.asAlgebraHom envelopeTraceAlgebra := by
  simp only [envelopeTraceOperator, envelopeTraceAlgebra, map_add,
    Representation.asAlgebraHom_single, one_smul]

theorem envelopeTraceOperator_apply (x : SymmetricEnvelope) :
    envelopeTraceOperator x = envelopeTrace x := by
  revert x
  decide +kernel

theorem envelopeTraceAlgebra_smul
    (x : symmetricEnvelopeRepresentation.asModule) :
    symmetricEnvelopeRepresentation.asModuleEquiv (envelopeTraceAlgebra • x) =
      ((symmetricEnvelopeRepresentation.asModuleEquiv x).1, 0, 0) := by
  rw [Representation.asModuleEquiv_map_smul, ← envelopeTraceOperator_eq,
    envelopeTraceOperator_apply, envelopeTrace_eq]

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
