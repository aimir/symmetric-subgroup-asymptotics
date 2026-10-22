import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductOrthogonality
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! Literal mixed zero-middle singular planes detect BOTH paired
components of every vector whose positive and negative projections are
nonzero. The same-coordinate support exception is handled explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleProbes
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBIntrinsicLongRoots
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem positive_basis_mem (n : ℕ) (i : Fin n) :
    (Pi.single (pos n i) 1 : Index n → K) ∈ positiveSubspace K n := by
  refine ⟨Pi.single i 1, ?_⟩
  funext j
  rcases j with (j | j) | ⟨⟩ <;> simp [positiveEmbedding, pos, Pi.single_apply]

omit [Finite K] in
theorem negative_basis_mem (n : ℕ) (i : Fin n) :
    (Pi.single (neg n i) 1 : Index n → K) ∈ negativeSubspace K n := by
  refine ⟨Pi.single i 1, ?_⟩
  funext j
  rcases j with (j | j) | ⟨⟩ <;> simp [negativeEmbedding, neg, Pi.single_apply]

theorem pairing_positive (n : ℕ) (v : Index n → K) (i : Fin n) :
    (gram K n).toBilin' v (Pi.single (pos n i) 1) = 2 * v (neg n i) := by
  rw [gram_pairing_symmetric n]
  exact CFSGOrthogonalBParabolicColumn.pairing_positive K n i v

theorem pairing_negative (n : ℕ) (v : Index n → K) (i : Fin n) :
    (gram K n).toBilin' v (Pi.single (neg n i) 1) = 2 * v (pos n i) := by
  rw [gram_pairing_symmetric n]
  simp [Matrix.toBilin'_apply, gram, pos, neg, Fintype.sum_sum_type, Pi.single_apply, ite_mul]

theorem basis_cross_pairing (n : ℕ) (i j : Fin n) :
    (gram K n).toBilin' (Pi.single (pos n i) 1) (Pi.single (neg n j) 1) =
      if i = j then 2 else 0 := by
  rw [pairing_negative]
  by_cases hij : i = j <;> simp [Pi.single_apply, hij, pos]

theorem exists_mixed_probes (h2 : (2 : K) ≠ 0) (s : ℕ) (v : Index (s + 3) → K)
    (hx : positivePart K (s + 3) v ≠ 0) (hy : negativePart K (s + 3) v ≠ 0) :
    ∃ a b : Index (s + 3) → K,
      a ∈ positiveSubspace K (s + 3) ∧ b ∈ negativeSubspace K (s + 3) ∧
      (gram K (s + 3)).toBilin' a b = 0 ∧
      (gram K (s + 3)).toBilin' v a ≠ 0 ∧ (gram K (s + 3)).toBilin' v b ≠ 0 := by
  classical
  have hex : ∃ i, v (pos (s + 3) i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (funext h)
  have hey : ∃ i, v (neg (s + 3) i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext h)
  by_cases hoff : ∃ i j, v (pos (s + 3) i) ≠ 0 ∧ v (neg (s + 3) j) ≠ 0 ∧ i ≠ j
  · obtain ⟨i, j, hi, hj, hij⟩ := hoff
    refine ⟨Pi.single (pos (s + 3) j) 1, Pi.single (neg (s + 3) i) 1,
      positive_basis_mem K _ j, negative_basis_mem K _ i, ?_, ?_, ?_⟩
    · rw [basis_cross_pairing, if_neg (Ne.symm hij)]
    · rw [pairing_positive]; exact mul_ne_zero h2 hj
    · rw [pairing_negative]; exact mul_ne_zero h2 hi
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨k, hk⟩ := hey
    have hki : k = i := by
      by_contra hki
      exact hoff ⟨i, k, hi, hk, Ne.symm hki⟩
    subst k
    have hjex : ∃ j : Fin (s + 3), j ≠ i := by
      by_cases hi0 : i.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro he
        have he' := congrArg Fin.val he
        change 1 = i.val at he'
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro he
        exact hi0 (congrArg Fin.val he).symm
    obtain ⟨j, hji⟩ := hjex
    have hxj : v (pos (s + 3) j) = 0 := by
      by_contra h
      exact hoff ⟨j, i, h, hk, hji⟩
    have hyj : v (neg (s + 3) j) = 0 := by
      by_contra h
      exact hoff ⟨i, j, hi, h, Ne.symm hji⟩
    refine ⟨Pi.single (pos (s + 3) i) 1 + Pi.single (pos (s + 3) j) 1,
      Pi.single (neg (s + 3) i) 1 - Pi.single (neg (s + 3) j) 1,
      (positiveSubspace K _).add_mem (positive_basis_mem K _ i) (positive_basis_mem K _ j),
      (negativeSubspace K _).sub_mem (negative_basis_mem K _ i) (negative_basis_mem K _ j), ?_, ?_, ?_⟩
    · simp only [map_add, map_sub, LinearMap.add_apply, basis_cross_pairing,
        if_neg hji, if_neg (Ne.symm hji)]
      ring
    · rw [map_add, pairing_positive, pairing_positive, hyj, mul_zero, add_zero]
      exact mul_ne_zero h2 hk
    · rw [map_sub, pairing_negative, pairing_negative, hxj, mul_zero, sub_zero]
      exact mul_ne_zero h2 hi

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleProbes
