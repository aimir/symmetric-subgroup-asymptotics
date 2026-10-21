import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! Symmetric matrices send a fixed nonzero vector onto every vector.
The rank-two formula is valid even in characteristic two. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixVector
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]
open scoped Matrix BigOperators

theorem exists_symmetric_mulVec (y z : I → K) (hy : y ≠ 0) :
    ∃ S : Matrix I I K, S.IsSymm ∧ S *ᵥ y = z := by
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    apply hy
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let w : I → K := Pi.single j (y j)⁻¹
  let c : K := ∑ k, z k * y k
  have hw : ∑ k, w k * y k = 1 := by
    simp [w, Pi.single_apply, ite_mul, hj]
  let S : Matrix I I K := fun i k => z i * w k + w i * z k - c * w i * w k
  refine ⟨S, Matrix.IsSymm.ext ?_, ?_⟩
  · intro i k
    change z k * w i + w k * z i - c * w k * w i =
      z i * w k + w i * z k - c * w i * w k
    ring
  · funext i
    change (∑ k, (z i * w k + w i * z k - c * w i * w k) * y k) = z i
    calc
      _ = z i * (∑ k, w k * y k) + w i * (∑ k, z k * y k) -
          (c * w i) * (∑ k, w k * y k) := by
        simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum, mul_assoc]
      _ = z i := by rw [hw]; dsimp [c]; ring

end SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixVector
