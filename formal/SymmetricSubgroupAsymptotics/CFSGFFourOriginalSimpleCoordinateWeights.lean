import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixEntryWeights
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleImageCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSeparatingCartan
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyProfile

/-! The existing actual simple unit entries are Cartan eigenfunctionals
on arbitrary E6 matrices. Diagonality plus the checked simple image unit
coordinate identifies the weights, with no root-coordinate census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleCoordinateWeights
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGFFourOriginalSimpleImageCoordinates CFSGFFourOriginalSeparatingCartan
open CFSGFFourOriginalRootFamilyProfile CFSGDiagonalMatrixEntryWeights
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def simpleCoordinate (i:Fin 4) : Mat→ₗ[ℚ]ℚ where
  toFun M:=coordinates M i
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private theorem e6_cartan_isDiag (i:Fin 6) : (e6H i).IsDiag := by
  change (RootPairing.GeckConstruction.h (E6Index i)).IsDiag
  rw [RootPairing.GeckConstruction.h_eq_diagonal]
  exact Matrix.isDiag_diagonal _

theorem cartan_isDiag (b:Fin 4) : (cartan b).IsDiag := by
  fin_cases b
  · exact (e6_cartan_isDiag 0).add (e6_cartan_isDiag 5)
  · exact (e6_cartan_isDiag 2).add (e6_cartan_isDiag 4)
  · exact e6_cartan_isDiag 3
  · exact e6_cartan_isDiag 1

theorem simple_cartan_coordinate (i b:Fin 4) (M:Mat) :
    simpleCoordinate i ⁅cartan b,M⁆=(A b i:ℚ)*simpleCoordinate i M := by
  change ⁅cartan b,M⁆ (row i) (col i)=(A b i:ℚ)*M (row i) (col i)
  apply entry_weight_of_unit_seed (cartan b) (cartan_isDiag b) (positive i)
    (row i) (col i) (A b i:ℚ) ?_ ?_ M
  · simpa only [if_pos rfl] using positive_coordinate i i
  · simpa only [Int.cast_smul_eq_zsmul] using HE b i

private theorem simple_testWeight : ∀i:Fin 4,
    testWeight (simpleIndex i)=∑b:Fin 4,coefficients b*A b i := by decide +kernel

private theorem testCartan_image : rationalRepresentation testCartan=
    ∑b:Fin 4,(coefficients b:ℚ) • cartan b := by
  rw [testCartan,map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_smul]
  change (coefficients b:ℚ) • rationalRepresentation (generator A (.H b))=_
  rw [rationalRepresentation_H]

theorem simple_testCartan_coordinate (i:Fin 4) (M:Mat) :
    simpleCoordinate i ⁅rationalRepresentation testCartan,M⁆=
      (testWeight (simpleIndex i):ℚ)*simpleCoordinate i M := by
  rw [testCartan_image,sum_lie,map_sum]
  simp only [smul_lie,map_smul,simple_cartan_coordinate,smul_eq_mul,←mul_assoc]
  rw [←Finset.sum_mul]
  have h:=congrArg (fun z:ℤ=>(z:ℚ)) (simple_testWeight i)
  simp only [Int.cast_sum,Int.cast_mul] at h
  rw [h]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSimpleCoordinateWeights
