import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! A unit preserving each literal grading block normalizes the subgroup
acting trivially on the associated graded space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
open CFSGGradedMatrixSupport
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem preserving_mul_strict_zero (weight : I→ℤ) (P X : Matrix I I K)
    (hP : Supported weight id P)
    (hX : ∀ i j,weight i≤weight j→X i j=0) :
    ∀ i j,weight i≤weight j→(P*X) i j=0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : weight i=weight k
  · rw [hX k j (by omega),mul_zero]
  · rw [hP i k hik,zero_mul]

theorem strict_zero_mul_preserving (weight : I→ℤ) (X P : Matrix I I K)
    (hX : ∀ i j,weight i≤weight j→X i j=0)
    (hP : Supported weight id P) :
    ∀ i j,weight i≤weight j→(X*P) i j=0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkj : weight k=weight j
  · rw [hX i k (by omega),zero_mul]
  · rw [hP k j hkj,mul_zero]

theorem preserving_conjugate_strict (weight : I→ℤ)
    (p u : (Matrix I I K)ˣ) (hp : p∈preservingUnits weight)
    (hu : u∈strictUnits weight) : p*u*p⁻¹∈strictUnits weight := by
  have hX : ∀ i j,weight i≤weight j→
      ((u : Matrix I I K)-1) i j=0 := by
    intro i j hij
    rw [Matrix.sub_apply,hu i j hij,sub_self]
  have hpi : Supported weight id (↑(p⁻¹) : Matrix I I K) :=
    (preservingUnits weight).inv_mem hp
  have hz := strict_zero_mul_preserving weight _ _
    (preserving_mul_strict_zero weight _ _ hp hX) hpi
  have he : ((p*u*p⁻¹ : (Matrix I I K)ˣ) : Matrix I I K)-1=
      (p : Matrix I I K)*((u : Matrix I I K)-1)*(↑(p⁻¹) : Matrix I I K) := by
    change (p : Matrix I I K)*(u : Matrix I I K)*(↑(p⁻¹) : Matrix I I K)-1=_
    rw [mul_sub,sub_mul,mul_one,Units.mul_inv]
  intro i j hij
  apply sub_eq_zero.mp
  have hh := congrArg (fun M : Matrix I I K=>M i j) he
  change ((p*u*p⁻¹ : (Matrix I I K)ˣ) : Matrix I I K) i j-
    (1 : Matrix I I K) i j=_ at hh
  rw [hh]
  exact hz i j hij

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
