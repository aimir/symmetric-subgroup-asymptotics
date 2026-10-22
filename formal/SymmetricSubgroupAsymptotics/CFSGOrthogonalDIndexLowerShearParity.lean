import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingRank
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Every literal lower shear preserving the actual split quadratic
form has even component distance. Its intersection is the actual shear
kernel; quadratic preservation makes the corresponding bilinear form
alternating, so the checked even-rank theorem applies also in char 2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexLowerShearParity
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexAlternatingRank
open CFSGOrthogonalDIndexSingularComponents CFSGMatrixShearUnits
variable (K : Type) [Field K]

def shearForm (r : ℕ) (S : Matrix (Fin r) (Fin r) K) :
    LinearMap.BilinForm K (Fin r → K) :=
  (Matrix.toBilin' (1 : Matrix (Fin r) (Fin r) K)).compl₁₂ (Matrix.mulVecLin S) LinearMap.id

theorem shearForm_apply (r : ℕ) (S : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    shearForm K r S x y = (S *ᵥ x) ⬝ᵥ y := by
  change Matrix.toBilin' (1 : Matrix (Fin r) (Fin r) K) (S *ᵥ x) y = _
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]

theorem shearForm_kernel (r : ℕ) (S : Matrix (Fin r) (Fin r) K) :
    (shearForm K r S).ker = (Matrix.mulVecLin S).ker := by
  ext x
  constructor
  · intro hx
    change shearForm K r S x = 0 at hx
    change S *ᵥ x = 0
    funext i
    have h := LinearMap.congr_fun hx (Pi.single i 1)
    rw [shearForm_apply, dotProduct_single, mul_one] at h
    exact h
  · intro hx
    change S *ᵥ x = 0 at hx
    change shearForm K r S x = 0
    apply LinearMap.ext
    intro y
    rw [shearForm_apply, hx, zero_dotProduct]
    rfl

theorem shearForm_isAlt (r : ℕ) (S : Matrix (Fin r) (Fin r) K)
    (hQ : ∀ x, splitQuadraticForm K r (ambientLinearEquiv K r (lower S) x) =
      splitQuadraticForm K r x) : (shearForm K r S).IsAlt := by
  intro x
  have h := hQ (positiveEmbedding K r x)
  rw [lower_positive_apply, splitQuadraticForm_apply, splitQuadraticForm_apply] at h
  change x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ 0 at h
  rw [dotProduct_zero] at h
  rw [shearForm_apply]
  exact (dotProduct_comm (S *ᵥ x) x).trans h

theorem lower_even_distance (r : ℕ) (S : Matrix (Fin r) (Fin r) K)
    (hQ : ∀ x, splitQuadraticForm K r (ambientLinearEquiv K r (lower S) x) =
      splitQuadraticForm K r x) :
    Even (distance r (positiveSpace K r)
      ((positiveSpace K r).map (ambientLinearEquiv K r (lower S)).toLinearMap)) := by
  change Even (r - Module.finrank K ↥(positiveSpace K r ⊓ (positiveSpace K r).map
    (ambientLinearEquiv K r (lower S)).toLinearMap))
  rw [lower_intersection_finrank]
  have h := even_finrank_sub_kernel (shearForm K r S) (shearForm_isAlt K r S hQ)
  rw [shearForm_kernel] at h
  simpa using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexLowerShearParity
