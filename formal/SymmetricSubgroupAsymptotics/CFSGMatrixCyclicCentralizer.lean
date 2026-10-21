import Mathlib.Data.Matrix.Basis

/-! Elementary cyclic-vector tools for the actual commutant of matrices.
No irreducibility or algebraic-closure hypothesis is required. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer
variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem eigenvector_of_commutes (A B : Matrix I I R) (hAB : A * B = B * A)
    (v : I → R) (c : R) (hv : A *ᵥ v = c • v) :
    A *ᵥ (B *ᵥ v) = c • (B *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

theorem eigenvector_of_commutes_projection (A : Matrix I I R) (j : I)
    (hA : A * Matrix.single j j 1 = Matrix.single j j 1 * A) :
    A *ᵥ Pi.single j 1 = A j j • Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  by_cases hx : x = j
  · subst x
    simp [Matrix.col]
  · have h := congrArg (fun M : Matrix I I R => M x j) hA
    dsimp only at h
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne 1 j j x j hx] at h
    simpa [Matrix.col, Pi.single_apply, hx, Ne.symm hx] using h

end SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer
