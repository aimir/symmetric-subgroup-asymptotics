import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer

/-! A literal degree projection commutes with multiplication by a
block-preserving matrix. Conjugation therefore acts linearly on the
first layer, with no logarithm or exponential argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixGroupFirstLayer
variable {I V R : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [DecidableEq V] [CommRing R]

theorem degreePart_mul_left (weight : I → V) (d : V) (M N : Matrix I I R)
    (hM : Supported weight id M) :
    degreePart weight d (M*N) = M * degreePart weight d N := by
  apply Matrix.ext
  intro i j
  change (if weight i = weight j+d then ∑ k, M i k*N k j else 0) =
    ∑ k, M i k*(if weight k = weight j+d then N k j else 0)
  by_cases hij : weight i = weight j+d
  · rw [if_pos hij]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : weight i = weight k
    · rw [if_pos (hik.symm.trans hij)]
    · rw [hM i k hik, zero_mul, zero_mul]
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : weight i = weight k
    · have hkj : weight k ≠ weight j+d := fun h => hij (hik.trans h)
      rw [if_neg hkj, mul_zero]
    · rw [hM i k hik, zero_mul]

theorem degreePart_mul_right (weight : I → V) (d : V) (M N : Matrix I I R)
    (hN : Supported weight id N) :
    degreePart weight d (M*N) = degreePart weight d M * N := by
  apply Matrix.ext
  intro i j
  change (if weight i = weight j+d then ∑ k, M i k*N k j else 0) =
    ∑ k, (if weight i = weight k+d then M i k else 0)*N k j
  by_cases hij : weight i = weight j+d
  · rw [if_pos hij]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkj : weight k = weight j
    · rw [if_pos (hij.trans (congrArg (fun w => w+d) hkj.symm))]
    · rw [hN k j hkj, mul_zero, mul_zero]
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkj : weight k = weight j
    · have hik : weight i ≠ weight k+d := fun h =>
        hij (h.trans (congrArg (fun w => w+d) hkj))
      rw [if_neg hik, zero_mul]
    · rw [hN k j hkj, mul_zero]

theorem firstLayer_conjugate (K : Type*) [Field K] (weight : I → ℤ)
    (p u : (Matrix I I K)ˣ)
    (hp : Supported weight id p.val) (hpinv : Supported weight id (p⁻¹).val) :
    firstLayer weight (p*u*p⁻¹) = p.val * firstLayer weight u * (p⁻¹).val := by
  have hdev : p.val*u.val*(p⁻¹).val-1 = p.val*(u.val-1)*(p⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  change degreePart weight 1 (p.val*u.val*(p⁻¹).val-1) =
    p.val * degreePart weight 1 (u.val-1) * (p⁻¹).val
  rw [hdev, degreePart_mul_right _ _ _ _ hpinv, degreePart_mul_left _ _ _ _ hp]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection
