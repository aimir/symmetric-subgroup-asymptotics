import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCoordinateLeftInverse
import SymmetricSubgroupAsymptotics.SplitLinearTensorInjectivity
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv
import SymmetricSubgroupAsymptotics.CFSGSerreFaithfulImageRepresentation

/-! The actual original F4 integral coordinate left inverse survives
arbitrary scalar extension. The literal integer-matrix tensor map is an
equivalence, so the SAME original base-change map and its induced image
representation are faithful in every field, including characteristic two.
No ordinary F4 simplicity or rational-dimension argument is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalBaseChangeFaithful
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
open CFSGFFourOriginalIntegralCoordinateLeftInverse CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _

theorem integral_tensor_injective (K:Type*) [CommRing K] :
    Function.Injective ((integralRepresentation realizationData).baseChange K) :=
  SplitLinearTensorInjectivity.baseChange_injective
    (integralRepresentation realizationData) integralLeftInverse
    integralRepresentation_leftInverse K

theorem baseChange_injective (K:Type*) [CommRing K] :
    Function.Injective (baseChange realizationData K) := by
  intro x y he
  apply integral_tensor_injective K
  apply CFSGIntegerMatrixTensorEquiv.tensorMap_injective K Index
  exact he

theorem imageRepresentation_injective (K:Type) [Field K] :
    Function.Injective (imageRepresentation realizationData K) :=
  CFSGSerreFaithfulImageRepresentation.imageRepresentation_injective
    realizationData K (baseChange_injective K)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalBaseChangeFaithful
