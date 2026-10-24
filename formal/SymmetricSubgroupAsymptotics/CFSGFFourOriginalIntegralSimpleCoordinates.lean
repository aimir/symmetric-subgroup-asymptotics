import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOppositionCoordinates

/-! Actual integral simple coordinate maps, with the negative ones
transported by the SAME integral Geck Omega. Rational casting identifies
them with the checked signed unit functionals before any field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSimpleCoordinates
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGFFourOriginalSimpleImageCoordinates CFSGFFourOriginalSimpleCoordinateWeights
open CFSGFFourOriginalOppositionCoordinates
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def integerSimpleCoordinate (i:Fin 4) : IntMat→ₗ[ℤ]ℤ where
  toFun M:=M (row i) (col i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def integerOpposition : IntMat→ₗ[ℤ]IntMat where
  toFun M:=CFSGGeckIntegralMatrices.Omega E6Base*M*CFSGGeckIntegralMatrices.Omega E6Base
  map_add' M N:=by simp only [mul_add,add_mul]
  map_smul' a M:=by simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

def integerSignedCoordinate (neg:Bool) (i:Fin 4) : IntMat→ₗ[ℤ]ℤ :=
  if neg then (integerSimpleCoordinate i).comp integerOpposition else integerSimpleCoordinate i

theorem signed_coordinate_cast (neg:Bool) (i:Fin 4) (M:IntMat) :
    (integerSignedCoordinate neg i M:ℚ)=
      signedCoordinate neg i ((Int.castRingHom ℚ).mapMatrix M) := by
  cases neg
  · rfl
  · have h:=congrArg (simpleCoordinate i)
      (CFSGGeckIntegralMatrices.map_opposition E6Base M)
    exact h

theorem integerRoot_cast (neg:Bool) (i:Fin 4) :
    (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)=
      rationalRepresentation (rootVector A neg i) := by
  cases neg
  · change (Int.castRingHom ℚ).mapMatrix (integerE i)=
      rationalRepresentation (generator A (.E i))
    rw [map_integerE,rationalRepresentation_E]
  · change (Int.castRingHom ℚ).mapMatrix (integerF i)=
      rationalRepresentation (generator A (.F i))
    rw [map_integerF,rationalRepresentation_F]

theorem signed_integer_unit (neg:Bool) (i:Fin 4) :
    integerSignedCoordinate neg i (integerRoot neg i)=1 := by
  apply (Int.cast_injective (α:=ℚ))
  rw [Int.cast_one,signed_coordinate_cast,integerRoot_cast,signed_unit]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSimpleCoordinates
