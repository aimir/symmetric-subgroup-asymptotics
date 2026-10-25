import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits

/-! The strict associated-graded kernel is normalized by the same weak
triangular group, with repeated integer weights allowed. This is a literal
matrix support result; it assumes no parabolic or root-group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictNormal
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open scoped BigOperators
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

private theorem weak_mul_strict (w : I → ℤ) (A B : Matrix I I K)
    (hA : A.BlockTriangular (fun i => -w i))
    (hB : ∀ i j, w i ≤ w j → B i j = 0) :
    ∀ i j, w i ≤ w j → (A*B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i < w k
  · rw [hA (show -w k < -w i by omega), zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem strict_mul_weak (w : I → ℤ) (A B : Matrix I I K)
    (hA : ∀ i j, w i ≤ w j → A i j = 0)
    (hB : B.BlockTriangular (fun i => -w i)) :
    ∀ i j, w i ≤ w j → (A*B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i ≤ w k
  · rw [hA i k hik, zero_mul]
  · rw [hB (show -w j < -w k by omega), mul_zero]

theorem conjugate_mem (w : I → ℤ) (g u : (Matrix I I K)ˣ)
    (hg : g ∈ triangularUnits (fun i => -w i)) (hu : u ∈ strictUnits w) :
    g*u*g⁻¹ ∈ strictUnits w := by
  let D : Matrix I I K := (u : Matrix I I K)-1
  have hD : ∀ i j, w i ≤ w j → D i j = 0 := by
    intro i j hij
    change (u : Matrix I I K) i j - (1 : Matrix I I K) i j = 0
    exact sub_eq_zero.mpr (hu i j hij)
  have hgi : (↑(g⁻¹) : Matrix I I K).BlockTriangular (fun i => -w i) :=
    (triangularUnits (fun i => -w i)).inv_mem hg
  have hz := strict_mul_weak w ((g : Matrix I I K)*D) (↑(g⁻¹) : Matrix I I K)
    (weak_mul_strict w (g : Matrix I I K) D hg hD) hgi
  have hgg : (g : Matrix I I K)*(↑(g⁻¹) : Matrix I I K) = 1 := Units.mul_inv g
  have he : (g : Matrix I I K)*D*(↑(g⁻¹) : Matrix I I K) =
      (↑(g*u*g⁻¹) : Matrix I I K)-1 := by
    change (g : Matrix I I K)*((u : Matrix I I K)-1)*(↑(g⁻¹) : Matrix I I K) =
      (g : Matrix I I K)*(u : Matrix I I K)*(↑(g⁻¹) : Matrix I I K)-1
    rw [mul_sub, sub_mul, mul_one, hgg]
  intro i j hij
  have h := hz i j hij
  rw [he] at h
  exact sub_eq_zero.mp h

theorem triangular_le_normalizer (w : I → ℤ) :
    triangularUnits (K := K) (fun i => -w i) ≤
      Subgroup.normalizer (strictUnits (K := K) w : Set (Matrix I I K)ˣ) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg u hu
  exact conjugate_mem w g u hg hu

theorem comap_strict_normal {G : Type*} [Group G] (w : I → ℤ)
    (rho : G →* (Matrix I I K)ˣ)
    (htri : ∀ g, rho g ∈ triangularUnits (fun i => -w i)) :
    ((strictUnits w).comap rho).Normal := by
  constructor
  intro u hu g
  change rho (g*u*g⁻¹) ∈ strictUnits w
  rw [map_mul, map_mul, map_inv]
  exact conjugate_mem w (rho g) (rho u) (htri g) hu

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictNormal
