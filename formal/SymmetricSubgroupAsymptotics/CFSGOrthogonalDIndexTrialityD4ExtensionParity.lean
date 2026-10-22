import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CrossExtensions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace

/-! The two local residual ruling families agree with the GENUINE
intersection-parity components of maximal singular D4 spaces. Opposite
families meet in dimension3; the already-proved quadratic triangle
parity makes each individual ruling one component, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD2Coordinates CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexSingularParity
open CFSGOrthogonalDIndexSingularComponents
variable (K : Type) [Field K]

theorem maximalExtension_self_orthogonal (M : MaximalExtensions K) :
    LinearMap.BilinForm.orthogonal (splitQuadraticForm K 4).polarBilin M.val = M.val := by
  have hle : M.val ≤ LinearMap.BilinForm.orthogonal (splitQuadraticForm K 4).polarBilin M.val := by
    intro x hx y hy
    exact CFSGOrthogonalDIndexQuadraticNeighborPlane.polar_zero_of_singular
      (splitQuadraticForm K 4) M.val M.property.2.1 y x hy hx
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.BilinForm.finrank_orthogonal (splitQuadraticForm_nondegenerate K 4),
    naturalSpace_finrank, M.property.1]

theorem extension_distance_symm (M N : MaximalExtensions K) :
    distance 4 M.val N.val = distance 4 N.val M.val := by
  change 4 - Module.finrank K ↥(M.val ⊓ N.val) = 4 - Module.finrank K ↥(N.val ⊓ M.val)
  rw [inf_comm]

theorem extension_same_component_of_common_opposite (M N C : MaximalExtensions K)
    (hMC : distance 4 M.val C.val = 1) (hCN : distance 4 C.val N.val = 1) :
    Even (distance 4 M.val N.val) := by
  have ht := even_three_distances (splitQuadraticForm K 4) (splitQuadraticForm_nondegenerate K 4)
    4 (naturalSpace_finrank K 4) M.val C.val N.val
    (maximalExtension_self_orthogonal K M) (maximalExtension_self_orthogonal K C)
    (maximalExtension_self_orthogonal K N)
    (fun x => M.property.2.1 x.val x.property)
    (fun x => C.property.2.1 x.val x.property)
    (fun x => N.property.2.1 x.val x.property)
  change Even (distance 4 M.val C.val + distance 4 C.val N.val + distance 4 M.val N.val) at ht
  rw [hMC, hCN] at ht
  obtain ⟨t, ht⟩ := ht
  exact ⟨t - 1, by omega⟩

theorem column_row_extension_distance (p q : RulingParameters K) :
    distance 4 (columnMaximalExtension K p).val (rowMaximalExtension K q).val = 1 := by
  rw [distance, column_row_maximal_inf_finrank]

theorem column_column_extension_same_component (p p' : RulingParameters K) :
    Even (distance 4 (columnMaximalExtension K p).val (columnMaximalExtension K p').val) := by
  let q : RulingParameters K := Projectivization.mk K (Pi.single (0 : Fin 2) (1 : K)) (by simp)
  apply extension_same_component_of_common_opposite K _ _ (rowMaximalExtension K q)
  · exact column_row_extension_distance K p q
  · rw [extension_distance_symm]
    exact column_row_extension_distance K p' q

theorem row_row_extension_same_component (q q' : RulingParameters K) :
    Even (distance 4 (rowMaximalExtension K q).val (rowMaximalExtension K q').val) := by
  let p : RulingParameters K := Projectivization.mk K (Pi.single (0 : Fin 2) (1 : K)) (by simp)
  apply extension_same_component_of_common_opposite K _ _ (columnMaximalExtension K p)
  · rw [extension_distance_symm]
    exact column_row_extension_distance K p q
  · exact column_row_extension_distance K p q'

theorem column_row_extension_not_same_component (p q : RulingParameters K) :
    ¬Even (distance 4 (columnMaximalExtension K p).val (rowMaximalExtension K q).val) := by
  rw [column_row_extension_distance]
  norm_num

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
