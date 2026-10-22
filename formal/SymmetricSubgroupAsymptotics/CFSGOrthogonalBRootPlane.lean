import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Ring

/-! The literal displacement image of a nonidentity B highest root is
the original positive two-plane. This labels planes, not vector points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

def positiveVector (s : ℕ) (i : Fin (s + 3)) : Index (s + 3) → K :=
  Pi.single (pos (s + 3) i) 1

def standardRootPlane (s : ℕ) : Submodule K (Index (s + 3) → K) :=
  Submodule.span K {positiveVector (K := K) s 0, positiveVector s (secondIndex s)}

theorem highestRoot_displacement (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K)
    (v : Index (s + 3) → K) :
    (((highestRoot s a).val : Mat K (s + 3)) - 1) *ᵥ v =
      (a * v (neg (s + 3) (secondIndex s))) • positiveVector s 0 -
        (a * v (neg (s + 3) 0)) • positiveVector s (secondIndex s) := by
  rw [highestRoot_val h2, add_sub_cancel_left, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec, Matrix.single_mulVec]
  ext x
  simp only [Pi.smul_apply, Pi.sub_apply, positiveVector, Pi.single_apply,
    Function.update_apply, Pi.zero_apply, smul_eq_mul]
  split_ifs <;> ring

theorem highestRoot_displacement_range (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (((highestRoot s a).val : Mat K (s + 3)) - 1)) =
      standardRootPlane (K := K) s := by
  have h0 : positiveVector (K := K) s 0 ∈ standardRootPlane (K := K) s := by
    apply Submodule.subset_span
    exact Or.inl rfl
  have h1 : positiveVector (K := K) s (secondIndex s) ∈ standardRootPlane (K := K) s := by
    apply Submodule.subset_span
    exact Or.inr rfl
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, highestRoot_displacement h2]
    exact (standardRootPlane (K := K) s).sub_mem
      ((standardRootPlane (K := K) s).smul_mem (a * v (neg (s + 3) (secondIndex s))) h0)
      ((standardRootPlane (K := K) s).smul_mem (a * v (neg (s + 3) 0)) h1)
  · apply Submodule.span_le.mpr
    rintro y (hy | hy)
    · subst y
      refine ⟨a⁻¹ • Pi.single (neg (s + 3) (secondIndex s)) (1 : K), ?_⟩
      rw [Matrix.mulVecLin_apply, highestRoot_displacement h2]
      simp [Pi.single_apply, pos, neg, secondIndex, Fin.ext_iff, smul_eq_mul,
        mul_inv_cancel₀ ha]
    · rcases hy with rfl
      refine ⟨(-a⁻¹) • Pi.single (neg (s + 3) 0) (1 : K), ?_⟩
      rw [Matrix.mulVecLin_apply, highestRoot_displacement h2]
      simp [Pi.single_apply, pos, neg, secondIndex, Fin.ext_iff, smul_eq_mul,
        mul_inv_cancel₀ ha, mul_neg]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
