import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylMatrixEntries

/-! Sparse finite transitions act in the actual norm26 representation.
The computational labels reindex the proved basis bijectively; coefficient
certificates over F2 are transported to every characteristic-two field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylCoordinateSteps
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylBasisLabels
open CFSGFFourE6MiddleWeylMatrixEntries CFSGFFourE6NormMatrixAction
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6CharacteristicTwoNormImage
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance
variable (K : Type) [Field K] [CharP K 2]

def matrixAction : canonicalElementaryGroup realizationData K→*Matrix (Fin 26) (Fin 26) K where
  toFun g := (normMatrixAction K g).submatrix basisIndex basisIndex
  map_one' := by
    ext j k
    change normMatrixAction K 1 (basisIndex j) (basisIndex k)=(1:Matrix (Fin 26) (Fin 26) K) j k
    rw [map_one]
    simp only [Matrix.one_apply,basisIndex_bijective.1.eq_iff]
  map_mul' g h := by
    change (normMatrixAction K (g*h)).submatrix basisIndex basisIndex=_
    rw [map_mul]
    let e : Fin 26≃PairIndex := Equiv.ofBijective basisIndex basisIndex_bijective
    exact (Matrix.submatrix_mul_equiv (normMatrixAction K g) (normMatrixAction K h)
      basisIndex e basisIndex).symm

def supportVector (s : Finset (Fin 26)) : Fin 26→K := fun j=>if j∈s then 1 else 0

theorem support_transition (neg : Bool) (axis : Fin 4) (haxis : axis=1∨axis=2)
    (s t : Finset (Fin 26))
    (hstep : ∀j : Fin 26,(∑k ∈ s,oneEntry neg axis j k)=supportValue t j) :
    matrixAction K (foldedRoot K neg axis 1)*ᵥsupportVector K s=supportVector K t := by
  funext j
  change (∑k : Fin 26,matrixAction K (foldedRoot K neg axis 1) j k*supportVector K s k)=_
  simp only [supportVector,mul_ite,mul_one,mul_zero,Finset.sum_ite_mem_eq]
  calc
    (∑k ∈ s,matrixAction K (foldedRoot K neg axis 1) j k)=
        ∑k ∈ s,ZMod.castHom (dvd_refl 2) K (oneEntry neg axis j k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact normMatrixAction_middle_one_entry K neg axis haxis j k
    _=ZMod.castHom (dvd_refl 2) K (∑k ∈ s,oneEntry neg axis j k) := (map_sum _ _ _).symm
    _=ZMod.castHom (dvd_refl 2) K (supportValue t j) := congrArg (ZMod.castHom (dvd_refl 2) K) (hstep j)
    _=(if j∈t then 1 else 0) := by
      by_cases hj : j∈t <;> simp only [supportValue,hj,if_true,if_false,map_one,map_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylCoordinateSteps
