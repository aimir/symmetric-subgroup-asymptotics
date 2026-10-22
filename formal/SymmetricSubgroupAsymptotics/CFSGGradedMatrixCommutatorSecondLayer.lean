import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSecondLayerProducts
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer
import Mathlib.Tactic.Group

/-! The leading height-two coefficient of an ACTUAL positive-unit
commutator is exactly the Lie bracket of the two genuine height-one
coefficients. No logarithm, division or good-characteristic hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixSubgroups CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixSecondLayerProducts
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem commutator_firstLayer_zero (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight) :
    firstLayer weight (u*v*u⁻¹*v⁻¹)=0 := by
  have huv := (strictUnits weight).mul_mem hu hv
  have hui := (strictUnits weight).inv_mem hu
  have hvi := (strictUnits weight).inv_mem hv
  have huvu := (strictUnits weight).mul_mem huv hui
  calc
    _=firstLayer weight (u*v*u⁻¹)+firstLayer weight v⁻¹ :=
      firstLayer_mul weight _ _ huvu hvi
    _=(firstLayer weight u+firstLayer weight v+ -firstLayer weight u)+ -firstLayer weight v := by
      rw [firstLayer_mul weight (u*v) u⁻¹ huv hui,firstLayer_mul weight u v hu hv,
        firstLayer_inv weight u hu,firstLayer_inv weight v hv]
    _=0 := by abel

theorem commutator_secondLayer (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight) :
    degreePart weight (2:ℤ)
      (((u*v*u⁻¹*v⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)-1)=
        ⁅firstLayer weight u,firstLayer weight v⁆ := by
  let c : (Matrix I I K)ˣ := u*v*u⁻¹*v⁻¹
  let C : Matrix I I K := (c : Matrix I I K)-1
  let D : Matrix I I K := (v : Matrix I I K)*(u : Matrix I I K)-1
  let M : Matrix I I K := (u : Matrix I I K)-1
  let N : Matrix I I K := (v : Matrix I I K)-1
  have hc : c∈strictUnits weight := (strictUnits weight).mul_mem
    ((strictUnits weight).mul_mem ((strictUnits weight).mul_mem hu hv)
      ((strictUnits weight).inv_mem hu)) ((strictUnits weight).inv_mem hv)
  have hhigh := height_two_of_firstLayer_zero weight c hc
    (commutator_firstLayer_zero weight u v hu hv)
  have hC : ∀i j,weight i≤weight j+1→C i j=0 := by
    intro i j hij
    change (c : Matrix I I K) i j-(1 : Matrix I I K) i j=0
    rw [hhigh i j hij,sub_self]
  have hD : Positive weight D := deviation_positive weight (v*u)
    ((strictUnits weight).mul_mem hv hu)
  have hM : Positive weight M := deviation_positive weight u hu
  have hN : Positive weight N := deviation_positive weight v hv
  have hg : c*v*u=u*v := by dsimp only [c];group
  have hm := congrArg (fun x : (Matrix I I K)ˣ=>(x : Matrix I I K)) hg
  change (c : Matrix I I K)*(v : Matrix I I K)*(u : Matrix I I K)=
    (u : Matrix I I K)*(v : Matrix I I K) at hm
  have hCV : C*((v : Matrix I I K)*(u : Matrix I I K))=
      (u : Matrix I I K)*(v : Matrix I I K)-(v : Matrix I I K)*(u : Matrix I I K) := by
    dsimp only [C]
    rw [sub_mul,one_mul,←mul_assoc,hm]
  have hring : C*(1+D)=M*N-N*M := by
    have hd : (1 : Matrix I I K)+D=(v : Matrix I I K)*(u : Matrix I I K) := by
      dsimp only [D]
      abel
    rw [hd,hCV]
    dsimp only [M,N]
    noncomm_ring
  have hh := congrArg (degreePart weight (2:ℤ)) hring
  rw [mul_add,mul_one,map_add,
    secondPart_height_two_times_positive_zero weight C D hC hD,add_zero] at hh
  simp only [map_sub] at hh
  rw [
    secondPart_positive_product weight M N hM hN,
    secondPart_positive_product weight N M hN hM] at hh
  simpa only [C,M,N,c,firstLayer,Ring.lie_def,map_sub] using hh

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer
