import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSimpleCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootCoordinateOrthogonality

/-! Integral root-coordinate maps on actual E6 integer matrices. Their
unit and crosszero values are cast from the checked rational weight proof,
yielding exact integer Kronecker coordinates BEFORE field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralRootCoordinates
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalUnitLoweringPaths
open CFSGFFourOriginalIntegralSimpleCoordinates CFSGFFourOriginalOppositionCoordinates
open CFSGFFourOriginalRootCoordinateOrthogonality
open CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _

def integerMatrixWord (neg:Bool) : List (Fin 4)→Module.End ℤ IntMat
  | []=>1
  | i::ss=>integerMatrixWord neg ss*LieAlgebra.ad ℤ IntMat (integerRoot neg i)

theorem matrix_word_cast (neg:Bool) (ss:List (Fin 4)) (M:IntMat) :
    (Int.castRingHom ℚ).mapMatrix (integerMatrixWord neg ss M)=
      matrixWord neg ss ((Int.castRingHom ℚ).mapMatrix M) := by
  induction ss generalizing M with
  | nil=>rfl
  | cons i ss ih=>
    change (Int.castRingHom ℚ).mapMatrix (integerMatrixWord neg ss ⁅integerRoot neg i,M⁆)=
      matrixWord neg ss ⁅rationalRepresentation (rootVector CartanMatrix.F₄ neg i),
        (Int.castRingHom ℚ).mapMatrix M⁆
    rw [ih]
    congr 1
    simp only [Ring.lie_def,map_sub,map_mul,integerRoot_cast]

def integerRootCoordinate (neg:Bool) (j:Fin 24) : IntMat→ₗ[ℤ]ℤ :=
  pathCoefficient j • (integerSignedCoordinate neg (terminalNode j)).comp
    (integerMatrixWord (!neg) (loweringSteps j))

theorem root_coordinate_cast (neg:Bool) (j:Fin 24) (M:IntMat) :
    (integerRootCoordinate neg j M:ℚ)=
      rootCoordinate neg j ((Int.castRingHom ℚ).mapMatrix M) := by
  change ((pathCoefficient j*integerSignedCoordinate neg (terminalNode j)
    (integerMatrixWord (!neg) (loweringSteps j) M):ℤ):ℚ)=
    (pathCoefficient j:ℚ) • signedCoordinate neg (terminalNode j)
      (matrixWord (!neg) (loweringSteps j) ((Int.castRingHom ℚ).mapMatrix M))
  simp only [Int.cast_mul,signed_coordinate_cast,matrix_word_cast,smul_eq_mul]

theorem coordinate_integral_vector (neg:Bool) (j:Fin 24) (k:BasisIndex) :
    integerRootCoordinate neg j (integralRepresentation realizationData (integralVectors k))=
      if k=.inl (neg,j) then 1 else 0 := by
  apply (Int.cast_injective (α:=ℚ))
  rw [root_coordinate_cast]
  have hc:=integralRepresentation_cast realizationData (integralVectors k)
  change (Int.castRingHom ℚ).mapMatrix (integralRepresentation realizationData (integralVectors k))=
    rationalRepresentation (vectors k) at hc
  rw [hc]
  change rootCoordinate neg j (rationalRepresentation (vectors k))=
    ((if k=.inl (neg,j) then 1 else 0:ℤ):ℚ)
  rw [root_coordinate_vector]
  split_ifs <;> rfl

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralRootCoordinates
