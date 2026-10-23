import SymmetricSubgroupAsymptotics.CFSGTrialityD4NormTwo
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIntegral
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceCoefficients
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! A quadratic Geck realization of the PINNED original D4 Serre source,
with genuine triality covariance on its rational quotient, original
integral lattice and every tensor base change. The exact source-Cartan
transport is proved; no source injectivity or fixed-group recognition
is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
open CFSG.Models.Chevalley CFSGTrialityD4NormTwo CFSGSerreDiagram
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCoordinateDiagramIntegral
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)):=Classical.decEq _

abbrev GeckIndex:=Base.support⊕CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)

def rawData:=realizationData (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
  D4_positive_definite Base Index

def data : Data (CartanMatrix.D 4) GeckIndex:=transportSource cartan_eq rawData

def trialityIndex : Equiv.Perm GeckIndex:=combinedIndex (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
  (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
  trialityPermutation triality_preserves

theorem integerGenerator_triality (g : CartanMatrix.Generators (Fin 4)) :
    Matrix.reindexAlgEquiv ℤ ℤ trialityIndex (data.integerGenerator g)=
      data.integerGenerator (nodeRename trialityPermutation g) := by
  simp only [data,transportSource_integerGenerator]
  exact integerGenerator_covariance (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    trialityPermutation triality_preserves g

theorem rational_triality_covariance (x : RationalLie (CartanMatrix.D 4)) :
    Matrix.reindexAlgEquiv ℚ ℚ trialityIndex (data.rational x)=
      data.rational (rationalEquiv (CartanMatrix.D 4) trialityPermutation triality_preserves x) :=
  CFSGSerreQuadraticDiagramIntertwining.rational_intertwining data trialityPermutation
    triality_preserves trialityIndex integerGenerator_triality x

theorem integral_triality_covariance (x : integralLattice (CartanMatrix.D 4)) :
    Matrix.reindexAlgEquiv ℤ ℤ trialityIndex (integralRepresentation data x)=
      integralRepresentation data
        (integralEquiv (CartanMatrix.D 4) trialityPermutation triality_preserves x) :=
  CFSGSerreQuadraticDiagramIntertwining.integral_intertwining data trialityPermutation
    triality_preserves trialityIndex integerGenerator_triality x

theorem tensor_triality_covariance (K : Type*) [CommRing K]
    (x : K⊗[ℤ]integralLattice (CartanMatrix.D 4)) :
    Matrix.reindexAlgEquiv K K trialityIndex (baseChange data K x)=
      baseChange data K ((integralEquiv (CartanMatrix.D 4) trialityPermutation
        triality_preserves).baseChange ℤ K (integralLattice (CartanMatrix.D 4))
          (integralLattice (CartanMatrix.D 4)) x) :=
  CFSGSerreQuadraticDiagramIntertwining.baseChange_intertwining data trialityPermutation
    triality_preserves trialityIndex integerGenerator_triality K x

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
