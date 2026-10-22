import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductOrthogonality

/-! The literal original odd-B Gram form is nondegenerate, proved by
its actual positive, negative and middle coordinate tests. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K] [Finite K]

theorem gram_nondegenerate (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (gram K n).toBilin'.Nondegenerate := by
  have hr (v : Index n → K) (hv : ∀ u, (gram K n).toBilin' u v = 0) : v = 0 := by
    funext x
    rcases x with (i | i) | ⟨⟩
    · have he := hv (Pi.single (neg n i) 1)
      have hz : (2 : K) * v (pos n i) = 0 := by
        simpa [Matrix.toBilin'_apply, gram, pos, neg, Fintype.sum_sum_type,
          Pi.single_apply, ite_mul] using he
      exact (mul_eq_zero.mp hz).resolve_left h2
    · have he := hv (Pi.single (pos n i) 1)
      have hz : (2 : K) * v (neg n i) = 0 := by
        simpa [Matrix.toBilin'_apply, gram, pos, neg, Fintype.sum_sum_type,
          Pi.single_apply, ite_mul] using he
      exact (mul_eq_zero.mp hz).resolve_left h2
    · have he := hv (Pi.single (middle n) 1)
      simpa [Matrix.toBilin'_apply, gram, middle, Fintype.sum_sum_type,
        Pi.single_apply, ite_mul] using he
  refine ⟨?_, hr⟩
  intro v hv
  apply hr v
  intro u
  exact (gram_pairing_symmetric n u v).trans (hv u)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
