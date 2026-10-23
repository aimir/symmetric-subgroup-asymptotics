import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceAction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist

/-! The actual E6 diagram--field twist preserves the full literal
matrix group. Its original simple-root and parameter formula is supplied
by proved integral E6 covariance, including both signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateDiagramIntegral CFSGSerreQuadraticMatrix CFSGSerreDiagram

theorem integer_root_diagram (neg : Bool) (i : Fin 6) :
    Matrix.reindexAlgEquiv ℤ ℤ diagramIndex (integerRoot rawData neg i)=
      integerRoot rawData neg (e6Permutation i) :=
  integerRoot_covariance CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves neg i

abbrev matrixTwist (K : Type*) [CommRing K] (sigma : K≃+*K) :=
  CFSGSerreQuadraticDiagramFieldTwist.matrixTwist diagramIndex K sigma
abbrev unitTwist (K : Type*) [CommRing K] (sigma : K≃+*K) :=
  CFSGSerreQuadraticDiagramFieldTwist.unitTwist diagramIndex K sigma

theorem unitTwist_root (K : Type*) [CommRing K] (sigma : K≃+*K)
    (neg : Bool) (i : Fin 6) (t : K) :
    unitTwist K sigma (canonicalRoot rawData K neg i t)=
      canonicalRoot rawData K neg (e6Permutation i) (sigma t) :=
  CFSGSerreQuadraticDiagramFieldTwist.unitTwist_root rawData e6Permutation diagramIndex
    integer_root_diagram K sigma neg i t

abbrev matrixGroupTwist (K : Type) [Field K] (sigma : K≃+*K) : MulAut (MatrixGroup K) :=
  CFSGSerreQuadraticDiagramFieldTwist.elementaryTwist rawData e6Permutation diagramIndex
    integer_root_diagram K sigma

theorem matrixGroupTwist_val (K : Type) [Field K] (sigma : K≃+*K) (g : MatrixGroup K) :
    (matrixGroupTwist K sigma g).val=unitTwist K sigma g.val := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
