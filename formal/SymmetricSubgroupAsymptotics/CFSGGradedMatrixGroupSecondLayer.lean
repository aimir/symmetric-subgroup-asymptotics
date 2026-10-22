import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSecondLayerProducts
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer

/-! The second height layer is additive on the actual zero-first-layer
subgroup. These identities use only matrix support, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixSubgroups CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixSecondLayerProducts
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def secondLayer (weight : I→ℤ) (u : (Matrix I I K)ˣ) : Matrix I I K :=
  degreePart weight (2:ℤ) ((u : Matrix I I K)-1)

theorem secondLayer_one (weight : I→ℤ) :
    secondLayer weight (1 : (Matrix I I K)ˣ)=0 := by
  simp only [secondLayer,Units.val_one,sub_self,map_zero]

theorem secondLayer_mul (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight)
    (hu0 : firstLayer weight u=0) :
    secondLayer weight (u*v)=secondLayer weight u+secondLayer weight v := by
  have hhigh := height_two_of_firstLayer_zero weight u hu hu0
  have hM : ∀i j,weight i≤weight j+1→
      ((u : Matrix I I K)-1) i j=0 := by
    intro i j hij
    rw [Matrix.sub_apply,hhigh i j hij,sub_self]
  have he : (u : Matrix I I K)*(v : Matrix I I K)-1=
      ((u : Matrix I I K)-1)+((v : Matrix I I K)-1)+
        ((u : Matrix I I K)-1)*((v : Matrix I I K)-1) := by noncomm_ring
  simp only [secondLayer,Units.val_mul]
  rw [he,map_add,map_add,secondPart_height_two_times_positive_zero weight _ _ hM
    (deviation_positive weight v hv),add_zero]

theorem secondLayer_inv (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hu0 : firstLayer weight u=0) :
    secondLayer weight u⁻¹= -secondLayer weight u := by
  have hh := secondLayer_mul weight u u⁻¹ hu ((strictUnits weight).inv_mem hu) hu0
  rw [mul_inv_cancel,secondLayer_one] at hh
  calc
    _=(secondLayer weight u+secondLayer weight u⁻¹)-secondLayer weight u := by abel
    _=0-secondLayer weight u := by rw [←hh]
    _=_ := zero_sub _

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer
