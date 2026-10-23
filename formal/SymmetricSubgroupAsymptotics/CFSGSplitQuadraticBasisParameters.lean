import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic

/-! Exact norm and polar values of the original split quadratic form on
arbitrary-parameter positive and negative coordinate vectors, uniformly
in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPolarForm
variable (K : Type) [Field K]

theorem positive_parts {n : ℕ} (j : Fin n) (a : K) :
    leftPart K (Pi.single (Sum.inl j) a) = Pi.single j a ∧
      rightPart K (Pi.single (Sum.inl j) a) = 0 := by
  constructor <;> funext i <;>
    simp [leftPart, rightPart, Function.comp_apply, Pi.single_apply]

theorem negative_parts {n : ℕ} (j : Fin n) (a : K) :
    leftPart K (Pi.single (Sum.inr j) a) = 0 ∧
      rightPart K (Pi.single (Sum.inr j) a) = Pi.single j a := by
  constructor <;> funext i <;>
    simp [leftPart, rightPart, Function.comp_apply, Pi.single_apply]

theorem positive_norm {n : ℕ} (j : Fin n) (a : K) :
    splitQuadraticForm K n (Pi.single (Sum.inl j) a) = 0 := by
  rw [splitQuadraticForm_apply, splitQ, (positive_parts K j a).1, (positive_parts K j a).2,
    dotProduct_zero]

theorem negative_norm {n : ℕ} (j : Fin n) (a : K) :
    splitQuadraticForm K n (Pi.single (Sum.inr j) a) = 0 := by
  rw [splitQuadraticForm_apply, splitQ, (negative_parts K j a).1, (negative_parts K j a).2,
    zero_dotProduct]

theorem positive_polar {n : ℕ} (j : Fin n) (a : K) (v : Index n → K) :
    QuadraticMap.polar (splitQuadraticForm K n) (Pi.single (Sum.inl j) a) v =
      a * v (Sum.inr j) := by
  change (splitQuadraticForm K n).polarBilin (Pi.single (Sum.inl j) a) v = _
  rw [splitQuadraticForm_polar, CFSGOrthogonalDIndexPolarForm.polar,
    (positive_parts K j a).1, (positive_parts K j a).2,
    single_dotProduct, dotProduct_zero, add_zero]
  rfl

theorem negative_polar {n : ℕ} (j : Fin n) (a : K) (v : Index n → K) :
    QuadraticMap.polar (splitQuadraticForm K n) (Pi.single (Sum.inr j) a) v =
      a * v (Sum.inl j) := by
  change (splitQuadraticForm K n).polarBilin (Pi.single (Sum.inr j) a) v = _
  rw [splitQuadraticForm_polar, CFSGOrthogonalDIndexPolarForm.polar,
    (negative_parts K j a).1, (negative_parts K j a).2,
    zero_dotProduct, dotProduct_single, zero_add]
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters
