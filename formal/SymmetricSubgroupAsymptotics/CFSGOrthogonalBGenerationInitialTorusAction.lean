import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationDiagonalAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialDiagonalValues
import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! The two exact torus actions required by the odd B root filter.
The first torus fixes alpha and scales beta by g, while its actual
Coxeter conjugate scales both by g. The two tori commute as literal
diagonal matrices, independently of the Coxeter's retained signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialTorusAction
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationForkTorus CFSGOrthogonalBGenerationCoxeter
open CFSGOrthogonalBGenerationInitialDiagonalValues CFSGOrthogonalBGenerationDiagonalAction
variable (K : Type) [Field K]

theorem initialTorus_val (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) :
    ((initialTorus K h2 s g).val : Mat K (s + 3)) = Matrix.diagonal (initialDiagonal K s g) :=
  forkTorus_val K h2 (s + 1) g

def shiftedTorus (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) : (Mat K (s + 3))ˣ :=
  (coxeterWeyl K (s + 2)).val * (initialTorus K h2 s g).val * (coxeterWeyl K (s + 2)).val⁻¹

theorem shiftedTorus_val (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) :
    (shiftedTorus K h2 s g : Mat K (s + 3)) = Matrix.diagonal (shiftedDiagonal K s g) := by
  change ((coxeterWeyl K (s + 2)).val : Mat K (s + 3)) *
    ((initialTorus K h2 s g).val : Mat K (s + 3)) *
      (↑((coxeterWeyl K (s + 2)).val⁻¹) : Mat K (s + 3)) = _
  rw [initialTorus_val]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K (s + 2)).val (coxeterCycle (s + 2)).symm
    (coxeterSign K (s + 2) ∘ (coxeterCycle (s + 2)).symm) (initialDiagonal K s g)
    (coxeter_monomial K (s + 2))

theorem initialTorus_alpha (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) (a : K) :
    (initialTorus K h2 s g).val * alphaUnit K s a * (initialTorus K h2 s g).val⁻¹ =
      alphaUnit K s a := by
  have hv := initialDiagonal_values K s g
  have hh := alpha_diagonal_conjugation K s (initialTorus K h2 s g).val
    (initialDiagonal K s g) (initialTorus_val K h2 s g) 1 a
    (by rw [hv.1, hv.2.1, one_mul])
    (by rw [hv.2.2.1, hv.2.2.2.1, one_mul])
  simpa only [one_mul] using hh

theorem initialTorus_beta (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) (a : K) :
    (initialTorus K h2 s g).val * betaUnit K s a * (initialTorus K h2 s g).val⁻¹ =
      betaUnit K s ((g : K) * a) := by
  have hv := initialDiagonal_values K s g
  apply beta_diagonal_conjugation K s (initialTorus K h2 s g).val
    (initialDiagonal K s g) (initialTorus_val K h2 s g)
  · rw [hv.1, hv.2.2.2.2, mul_one]
  · rw [hv.2.2.2.2, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

theorem shiftedTorus_alpha (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) (a : K) :
    shiftedTorus K h2 s g * alphaUnit K s a * (shiftedTorus K h2 s g)⁻¹ =
      alphaUnit K s ((g : K) * a) := by
  have hv := shiftedDiagonal_values K s g
  apply alpha_diagonal_conjugation K s (shiftedTorus K h2 s g)
    (shiftedDiagonal K s g) (shiftedTorus_val K h2 s g)
  · rw [hv.1, hv.2.1, mul_one]
  · rw [hv.2.2.1, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

theorem shiftedTorus_beta (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) (a : K) :
    shiftedTorus K h2 s g * betaUnit K s a * (shiftedTorus K h2 s g)⁻¹ =
      betaUnit K s ((g : K) * a) := by
  have hv := shiftedDiagonal_values K s g
  apply beta_diagonal_conjugation K s (shiftedTorus K h2 s g)
    (shiftedDiagonal K s g) (shiftedTorus_val K h2 s g)
  · rw [hv.1, hv.2.2.2.2, mul_one]
  · rw [hv.2.2.2.2, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

theorem shiftedTorus_commute (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) :
    Commute (shiftedTorus K h2 s g) (initialTorus K h2 s g).val := by
  change shiftedTorus K h2 s g * (initialTorus K h2 s g).val =
    (initialTorus K h2 s g).val * shiftedTorus K h2 s g
  apply Units.ext
  change (shiftedTorus K h2 s g : Mat K (s + 3)) *
    ((initialTorus K h2 s g).val : Mat K (s + 3)) =
      ((initialTorus K h2 s g).val : Mat K (s + 3)) *
        (shiftedTorus K h2 s g : Mat K (s + 3))
  rw [shiftedTorus_val, initialTorus_val, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialTorusAction
