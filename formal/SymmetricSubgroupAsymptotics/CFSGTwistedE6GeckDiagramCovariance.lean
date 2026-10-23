import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIntegral
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceCoefficients
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! The pinned E6 diagram involution intertwines with the SAME original
E6 Serre realization on its rational quotient, integral lattice and
every tensor base change. This reuses the existing original E6Data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreQuadraticMatrix
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateDiagramIndices
open CFSGNormTwoCoordinateDiagramIntegral

abbrev GeckIndex := E6Base.support⊕CFSGNormTwoRootPairing.Roots CartanMatrix.E₆
abbrev rawData := realizationData CartanMatrix.E₆ CartanMatrix.E₆_transpose
  E6_positive_definite E6Base E6Index
abbrev data := E6Data

def diagramIndex : Equiv.Perm GeckIndex := combinedIndex CartanMatrix.E₆ CartanMatrix.E₆_diag
  CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves

theorem integerGenerator_diagram (g : CartanMatrix.Generators (Fin 6)) :
    Matrix.reindexAlgEquiv ℤ ℤ diagramIndex (data.integerGenerator g)=
      data.integerGenerator (nodeRename e6Permutation g) := by
  simp only [data,E6Data,transportSource_integerGenerator]
  exact integerGenerator_covariance CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves g

theorem rational_diagram_covariance (x : RationalLie CartanMatrix.E₆) :
    Matrix.reindexAlgEquiv ℚ ℚ diagramIndex (data.rational x)=
      data.rational (rationalEquiv CartanMatrix.E₆ e6Permutation e6_preserves x) :=
  CFSGSerreQuadraticDiagramIntertwining.rational_intertwining data e6Permutation e6_preserves
    diagramIndex integerGenerator_diagram x

theorem integral_diagram_covariance (x : integralLattice CartanMatrix.E₆) :
    Matrix.reindexAlgEquiv ℤ ℤ diagramIndex (integralRepresentation data x)=
      integralRepresentation data (integralEquiv CartanMatrix.E₆ e6Permutation e6_preserves x) :=
  CFSGSerreQuadraticDiagramIntertwining.integral_intertwining data e6Permutation e6_preserves
    diagramIndex integerGenerator_diagram x

theorem tensor_diagram_covariance (K : Type*) [CommRing K]
    (x : K⊗[ℤ]integralLattice CartanMatrix.E₆) :
    Matrix.reindexAlgEquiv K K diagramIndex (baseChange data K x)=
      baseChange data K ((integralEquiv CartanMatrix.E₆ e6Permutation e6_preserves).baseChange ℤ K
        (integralLattice CartanMatrix.E₆) (integralLattice CartanMatrix.E₆) x) :=
  CFSGSerreQuadraticDiagramIntertwining.baseChange_intertwining data e6Permutation e6_preserves
    diagramIndex integerGenerator_diagram K x

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
