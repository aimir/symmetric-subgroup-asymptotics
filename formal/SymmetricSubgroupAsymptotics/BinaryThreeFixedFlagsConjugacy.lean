import SymmetricSubgroupAsymptotics.BinaryThreeFixedSubgroups
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Fixed vector and fixed dual vector flags pull back under actual matrix
conjugation. The explicit transformed vectors retain their nonzero proofs. -/

set_option autoImplicit false
open scoped Matrix Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces

theorem fixed_vector_of_conjugate (U : Subgroup Ambient) (c : Ambient)
    (v : Vector) (hv : v ≠ 0)
    (hfix : ∀ g ∈ MulAut.conj c • U, g.val *ᵥ v = v) :
    ∃ w : Vector, w ≠ 0 ∧ ∀ g ∈ U, g.val *ᵥ w = w := by
  let w : Vector := c.inv *ᵥ v
  refine ⟨w, ?_, ?_⟩
  · have he : c.val *ᵥ w = v := by
      change c.val *ᵥ (c.inv *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, c.val_inv]
      simp
    intro hw
    rw [hw, Matrix.mulVec_zero] at he
    exact hv he.symm
  · intro g hg
    have hm : MulAut.conj c g ∈ MulAut.conj c • U :=
      Subgroup.smul_mem_pointwise_smul g (MulAut.conj c) U hg
    have he := hfix _ hm
    change (c.val * g.val * c.inv) *ᵥ v = v at he
    change g.val *ᵥ (c.inv *ᵥ v) = c.inv *ᵥ v
    calc
      _ = (g.val * c.inv) *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = (c.inv * (c.val * g.val * c.inv)) *ᵥ v := by
        simp only [← mul_assoc, c.inv_val, one_mul]
      _ = c.inv *ᵥ ((c.val * g.val * c.inv) *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = _ := by rw [he]

theorem fixed_covector_of_conjugate (U : Subgroup Ambient) (c : Ambient)
    (l : Vector) (hl : l ≠ 0)
    (hfix : ∀ g ∈ MulAut.conj c • U, l ᵥ* g.val = l) :
    ∃ w : Vector, w ≠ 0 ∧ ∀ g ∈ U, w ᵥ* g.val = w := by
  let w : Vector := l ᵥ* c.val
  refine ⟨w, ?_, ?_⟩
  · have he : w ᵥ* c.inv = l := by
      change (l ᵥ* c.val) ᵥ* c.inv = l
      rw [Matrix.vecMul_vecMul, c.val_inv]
      simp
    intro hw
    rw [hw, Matrix.zero_vecMul] at he
    exact hl he.symm
  · intro g hg
    have hm : MulAut.conj c g ∈ MulAut.conj c • U :=
      Subgroup.smul_mem_pointwise_smul g (MulAut.conj c) U hg
    have he := hfix _ hm
    change l ᵥ* (c.val * g.val * c.inv) = l at he
    change (l ᵥ* c.val) ᵥ* g.val = l ᵥ* c.val
    calc
      _ = l ᵥ* (c.val * g.val) := Matrix.vecMul_vecMul _ _ _
      _ = l ᵥ* ((c.val * g.val * c.inv) * c.val) := by
        simp only [mul_assoc, c.inv_val, mul_one]
      _ = (l ᵥ* (c.val * g.val * c.inv)) ᵥ* c.val :=
        (Matrix.vecMul_vecMul _ _ _).symm
      _ = _ := by rw [he]

end SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces
