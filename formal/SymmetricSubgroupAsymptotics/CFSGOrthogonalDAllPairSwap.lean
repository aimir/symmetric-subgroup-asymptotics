import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm

/-! The actual all-pairs exchange is a quadratic isometry and is
literally defining-fixed. Its elementary/component membership is not
asserted or needed for relative frame elimination. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllPairSwap
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGTwistedDNaturalFieldTwist CFSGOrthogonalDGenerationForkTorus
variable (K : Type) [Field K]

def pairSwap (r : ℕ) : (Mat K r)ˣ where
  val := Matrix.fromBlocks 0 1 1 0
  inv := Matrix.fromBlocks 0 1 1 0
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, mul_one, zero_add, add_zero]
    exact Matrix.fromBlocks_one
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, mul_one, zero_add, add_zero]
    exact Matrix.fromBlocks_one

theorem pairSwap_action (r : ℕ) (v : Index r → K) :
    (pairSwap K r : Mat K r) *ᵥ v = Sum.elim (v ∘ Sum.inr) (v ∘ Sum.inl) := by
  change Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 1 0 *ᵥ v = _
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]

theorem pairSwap_quadratic (r : ℕ) : pairSwap K r ∈ quadraticPreserving K r := by
  intro v
  rw [pairSwap_action]
  simp only [splitQ, leftPart, rightPart, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    dotProduct, mul_comm]

theorem pairSwap_twist (n : ℕ) (σ : K ≃+* K) :
    unitTwist K n σ (pairSwap K (n + 2)) = pairSwap K (n + 2) := by
  apply Units.ext
  ext x y
  change σ ((Matrix.fromBlocks (0 : Matrix (Fin (n + 2)) (Fin (n + 2)) K) 1 1 0)
    ((CFSGOrthogonalDGenerationForkTorus.flip n).symm x)
    ((CFSGOrthogonalDGenerationForkTorus.flip n).symm y)) = _
  have hs : (CFSGOrthogonalDGenerationForkTorus.flip n).symm =
      CFSGOrthogonalDGenerationForkTorus.flip n := Equiv.symm_swap _ _
  rw [hs]
  rcases x with i | i <;> rcases y with j | j <;>
    by_cases hi : i = last n <;> by_cases hj : j = last n <;>
    simp [CFSGOrthogonalDGenerationForkTorus.flip, Equiv.swap_apply_def,
      hi, hj, pairSwap, Matrix.fromBlocks, Matrix.one_apply, eq_comm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllPairSwap
