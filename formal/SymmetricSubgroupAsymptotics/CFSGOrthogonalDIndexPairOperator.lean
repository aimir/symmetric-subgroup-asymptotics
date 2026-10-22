import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
import SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement

/-! The actual D highest-root displacement is its literal alternating
pair operator, in every characteristic. Conjugation transports its
original two vectors by the SAME natural matrix action. There is no
factor two to cancel, so the statement includes characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexBundledQuadratic
open CFSGAlternatingPairOperator
variable (K : Type) [Field K]

def highestRoot (s : ℕ) (a : K) : elementaryRootGroup K (s + 4) :=
  (highestInU K s a).val

theorem highestRoot_displacement_pairOperator (s : ℕ) (a : K) :
    Matrix.mulVecLin (((highestRoot K s a).val : Mat K (s + 4)) - 1) =
      a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin
        (firstVector K s) (secondVector K s) := by
  change Matrix.mulVecLin (((highestInU K s a).val.val : Mat K (s + 4)) - 1) = _
  rw [highestInU_val, add_sub_cancel_left]
  apply LinearMap.ext
  intro x
  rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, highestDirection_mulVec]
  simp only [LinearMap.smul_apply, pairOperator_apply, splitQuadraticForm_polar, bivector]

theorem conjugate_highestRoot_displacement_pairOperator (s : ℕ)
    (g : elementaryRootGroup K (s + 4)) (a : K) :
    Matrix.mulVecLin (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1) =
      a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin
        ((g.val : Mat K (s + 4)) *ᵥ firstVector K s)
        ((g.val : Mat K (s + 4)) *ᵥ secondVector K s) := by
  let L := Matrix.mulVecLin (g.val : Mat K (s + 4))
  let R := Matrix.mulVecLin (↑(g.val⁻¹) : Mat K (s + 4))
  have hL (x y : Index (s + 4) → K) :
      (splitQuadraticForm K (s + 4)).polarBilin (L x) (L y) =
        (splitQuadraticForm K (s + 4)).polarBilin x y := by
    rw [splitQuadraticForm_polar, splitQuadraticForm_polar]
    exact elementary_preserves_polar K s g x y
  have hLR (x : Index (s + 4) → K) : L (R x) = x := by
    change (g.val : Mat K (s + 4)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 4)) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hc := pairOperator_conjugation (splitQuadraticForm K (s + 4)).polarBilin
    L R hL hLR (firstVector K s) (secondVector K s)
  change Matrix.mulVecLin
    (((g.val * (highestRoot K s a).val * g.val⁻¹ : (Mat K (s + 4))ˣ) : Mat K (s + 4)) - 1) = _
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one,
    Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, highestRoot_displacement_pairOperator]
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun hc x
  change L (pairOperator (splitQuadraticForm K (s + 4)).polarBilin
    (firstVector K s) (secondVector K s) (R x)) = _ at he
  change L (a • pairOperator (splitQuadraticForm K (s + 4)).polarBilin
    (firstVector K s) (secondVector K s) (R x)) = _
  rw [map_smul, he]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairOperator
