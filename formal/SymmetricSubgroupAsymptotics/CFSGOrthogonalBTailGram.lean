import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailVectorAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularCoordinates
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The original first-pair/tail coordinates preserve the original Gram
norm when the paired negative head is zero. The original tail action
fixes the first positive vector exactly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
variable (K : Type) [Field K]

theorem pairing_first_positive (n : ℕ) (v : Index (n + 1) → K) :
    (gram K (n + 1)).toBilin' (Pi.single (pos (n + 1) 0) 1) v =
      2 * v (neg (n + 1) 0) := by
  simp [Matrix.toBilin'_apply, gram, pos, neg, Fintype.sum_sum_type,
    Pi.single_apply, ite_mul]

theorem gram_norm_tail_of_negative_head_zero (n : ℕ) (v : Index (n + 1) → K)
    (hv : v (neg (n + 1) 0) = 0) :
    (gram K (n + 1)).toBilin' v v =
      (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n v) := by
  change v (Sum.inl (Sum.inr (0 : Fin (n + 1)))) = 0 at hv
  rw [gram_norm_coordinates, gram_norm_coordinates, Fin.sum_univ_succ]
  simp [positivePart, negativePart, tailRestriction, tailIndex, pos, neg, middle, hv]

theorem vector_eq_first_of_tail_zero (n : ℕ) (v : Index (n + 1) → K)
    (ht : tailRestriction K n v = 0) (hn : v (neg (n + 1) 0) = 0) :
    v = v (pos (n + 1) 0) • Pi.single (pos (n + 1) 0) 1 := by
  funext x
  rcases x with (i | i) | ⟨⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [pos]
    · have hh := congrFun ht (pos n j)
      simpa [tailRestriction, tailIndex, pos, Pi.single_apply] using hh
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa [pos, neg, Pi.single_apply] using hn
    · have hh := congrFun ht (neg n j)
      simpa [tailRestriction, tailIndex, pos, neg, Pi.single_apply] using hh
  · have hh := congrFun ht (middle n)
    simpa [tailRestriction, tailIndex, pos, middle, Pi.single_apply] using hh

theorem tailElementaryHom_fixes_first_positive (n : ℕ) (g : elementaryRootGroup K n) :
    ((tailElementaryHom K n g).val : Mat K (n + 1)) *ᵥ Pi.single (pos (n + 1) 0) 1 =
      Pi.single (pos (n + 1) 0) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  change tailMatrixHom K n (g.val : Mat K n) (tailEquiv n x) (tailEquiv n (Sum.inr 0)) =
    (Pi.single (tailEquiv n (Sum.inr 0)) (1 : K) : Index (n + 1) → K) (tailEquiv n x)
  rw [tailMatrixHom_apply_equiv]
  rcases x with i | j
  · have hne : tailEquiv n (Sum.inr 0) ≠ tailEquiv n (Sum.inl i) := by
      intro he
      cases (tailEquiv n).injective he
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Pi.single_apply, if_neg (Ne.symm hne)]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Pi.single_apply,
      (tailEquiv n).injective.eq_iff, Sum.inr.injEq]

theorem vector_eq_first_add_tail_basis (s : ℕ) (v : Index (s + 2) → K)
    (ht : tailRestriction K (s + 1) v = Pi.single (pos (s + 1) 0) 1)
    (hn : v (neg (s + 2) 0) = 0) :
    v = v (pos (s + 2) 0) • Pi.single (pos (s + 2) 0) 1 +
      Pi.single (pos (s + 2) (0 : Fin (s + 1)).succ) 1 := by
  funext x
  rcases x with (i | i) | ⟨⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [pos]
    · have hh := congrFun ht (pos (s + 1) j)
      have hsucc : j.succ = (1 : Fin (s + 2)) ↔ j = 0 := by
        change j.succ = (0 : Fin (s + 1)).succ ↔ j = 0
        exact Fin.succ_inj
      simpa [tailRestriction, tailIndex, pos, Pi.single_apply, eq_comm, hsucc] using hh
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa [pos, neg, Pi.single_apply] using hn
    · have hh := congrFun ht (neg (s + 1) j)
      simpa [tailRestriction, tailIndex, pos, neg, Pi.single_apply] using hh
  · have hh := congrFun ht (middle (s + 1))
    simpa [tailRestriction, tailIndex, pos, middle, Pi.single_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
