import SymmetricSubgroupAsymptotics.CFSGSymplecticPairPermutations
import SymmetricSubgroupAsymptotics.CFSGMonomialUnitCoordinates

/-! Exact natural matrix-coordinate transport by the actual pair
permutation words inside the elementary C model. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem pairPermutationUnit_monomial (K : Type) [Field K] (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) :
    (pairPermutationUnit K r σ : Mat K (r + 1)) =
      CFSGTypeAMonomialMatrices.monomial (pairedPermutation r σ).symm (fun _ => 1) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  have hb : (pairPermutationUnit K r σ : Mat K (r + 1)) *ᵥ Pi.single i 1 =
      Pi.single (pairedPermutation r σ i) 1 := by
    cases i with
    | inl j => exact pairPermutationUnit_basis K r σ false j
    | inr j => exact pairPermutationUnit_basis K r σ true j
  rw [hb]
  funext j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply,
    CFSGTypeAMonomialMatrices.monomial_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem pairPermutationUnit_single_conjugation (K : Type) [Field K] (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) (i j : Index (r + 1)) :
    (pairPermutationUnit K r σ : Mat K (r + 1)) * Matrix.single i j 1 *
      (↑((pairPermutationUnit K r σ)⁻¹) : Mat K (r + 1)) =
      Matrix.single (pairedPermutation r σ i) (pairedPermutation r σ j) 1 := by
  have h := CFSGMonomialUnitCoordinates.conjugation_single (pairPermutationUnit K r σ)
    (pairedPermutation r σ).symm (fun _ => (1 : K))
    (pairPermutationUnit_monomial K r σ) i j one_ne_zero
  simpa only [Equiv.symm_symm, div_one, one_smul] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
