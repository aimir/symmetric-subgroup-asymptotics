import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleCoordinateWeights
import SymmetricSubgroupAsymptotics.CFSGGeckIntegralOpposition

/-! Negative simple unit coordinates from the SAME integral Geck
opposition. This transports the known positive unit functional and its
Cartan weight; no additional matrix-entry census or source faithfulness
is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalOppositionCoordinates
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGFFourOriginalSimpleCoordinateWeights CFSGFFourOriginalSimpleImageCoordinates
open CFSGFFourOriginalSeparatingCartan CFSGFFourOriginalRootFamilyProfile
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def opposition : Mat≃ₐ[ℚ]Mat:=CFSGGeckOppositionAlgEquiv.opposition E6Base

theorem opposition_lie (M N:Mat) : opposition ⁅M,N⁆=⁅opposition M,opposition N⁆ := by
  simp only [Ring.lie_def,map_sub,map_mul]

theorem opposition_positive_eq (i:Fin 4) : opposition (positive i)=negative i :=
  CFSGFFourSerreMatrices.opposition_positive i

theorem opposition_negative (i:Fin 4) : opposition (negative i)=positive i := by
  have hh (j:Fin 6) : opposition (e6F j)=e6E j :=
    CFSGGeckOppositionAlgEquiv.opposition_F E6Base (E6Index j)
  fin_cases i
  · change opposition (e6F 0+e6F 5)=e6E 0+e6E 5
    rw [map_add,hh,hh]
  · change opposition (e6F 2+e6F 4)=e6E 2+e6E 4
    rw [map_add,hh,hh]
  · exact hh 3
  · exact hh 1

theorem opposition_cartan (i:Fin 4) : opposition (cartan i)= -cartan i := by
  have he:⁅positive i,negative i⁆=cartan i:=by simpa only [if_pos rfl] using EF i i
  rw [←he,opposition_lie,opposition_positive_eq,opposition_negative,
    ←lie_skew (negative i) (positive i),he]

def negativeCoordinate (i:Fin 4) : Mat→ₗ[ℚ]ℚ :=
  (simpleCoordinate i).comp opposition.toLinearEquiv.toLinearMap

theorem negative_unit (i:Fin 4) : negativeCoordinate i (negative i)=1 := by
  change simpleCoordinate i (opposition (negative i))=1
  rw [opposition_negative]
  change positive i (row i) (col i)=1
  simpa only [if_pos rfl] using positive_coordinate i i

theorem negative_cartan_coordinate (i b:Fin 4) (M:Mat) :
    negativeCoordinate i ⁅cartan b,M⁆= -(A b i:ℚ)*negativeCoordinate i M := by
  change simpleCoordinate i (opposition ⁅cartan b,M⁆)=
    -(A b i:ℚ)*simpleCoordinate i (opposition M)
  rw [opposition_lie,opposition_cartan,neg_lie,map_neg,simple_cartan_coordinate]
  ring

private theorem testCartan_image : rationalRepresentation testCartan=
    ∑b:Fin 4,(coefficients b:ℚ) • cartan b := by
  rw [testCartan,map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_smul]
  change (coefficients b:ℚ) • rationalRepresentation (generator A (.H b))=_
  rw [rationalRepresentation_H]

theorem opposition_testCartan : opposition (rationalRepresentation testCartan)=
    -rationalRepresentation testCartan := by
  simp only [testCartan_image,map_sum,map_smul,opposition_cartan,smul_neg,Finset.sum_neg_distrib]

theorem negative_testCartan_coordinate (i:Fin 4) (M:Mat) :
    negativeCoordinate i ⁅rationalRepresentation testCartan,M⁆=
      -(testWeight (simpleIndex i):ℚ)*negativeCoordinate i M := by
  change simpleCoordinate i (opposition ⁅rationalRepresentation testCartan,M⁆)=
    -(testWeight (simpleIndex i):ℚ)*simpleCoordinate i (opposition M)
  rw [opposition_lie,opposition_testCartan,neg_lie,map_neg,simple_testCartan_coordinate]
  ring

def signedCoordinate (neg:Bool) (i:Fin 4) : Mat→ₗ[ℚ]ℚ :=
  if neg then negativeCoordinate i else simpleCoordinate i

theorem signed_unit (neg:Bool) (i:Fin 4) :
    signedCoordinate neg i (rationalRepresentation (rootVector A neg i))=1 := by
  cases neg
  · change simpleCoordinate i (rationalRepresentation (generator A (.E i)))=1
    rw [rationalRepresentation_E]
    change positive i (row i) (col i)=1
    simpa only [if_pos rfl] using positive_coordinate i i
  · change negativeCoordinate i (rationalRepresentation (generator A (.F i)))=1
    rw [rationalRepresentation_F,negative_unit]

theorem signed_testCartan_coordinate (neg:Bool) (i:Fin 4) (M:Mat) :
    signedCoordinate neg i ⁅rationalRepresentation testCartan,M⁆=
      (if neg then -(testWeight (simpleIndex i):ℚ) else (testWeight (simpleIndex i):ℚ))*
        signedCoordinate neg i M := by
  cases neg
  · exact simple_testCartan_coordinate i M
  · exact negative_testCartan_coordinate i M

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalOppositionCoordinates
