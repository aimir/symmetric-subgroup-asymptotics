import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! Exact sparse products for a weighted permutation Gram matrix. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGWeightedPermutationGram
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

def gram (σ : Equiv.Perm I) (s : I→R) : Matrix I I R := fun i j=>if j=σ i then s i else 0

theorem gram_mul (σ : Equiv.Perm I) (s : I→R) (M : Matrix I I R) (i j : I) :
    (gram σ s*M) i j=s i*M (σ i) j := by
  simp [gram,Matrix.mul_apply,ite_mul]

theorem transpose_mul_gram (σ : Equiv.Perm I) (s : I→R) (M : Matrix I I R) (i j : I) :
    (M.transpose*gram σ s) i j=M (σ.symm j) i*s (σ.symm j) := by
  have he (k : I) : j=σ k ↔ k=σ.symm j := by
    constructor
    · intro h
      simpa only [Equiv.symm_apply_apply] using (congrArg σ.symm h).symm
    · intro h
      subst k
      exact (σ.apply_symm_apply j).symm
  simp only [Matrix.mul_apply,Matrix.transpose_apply,gram]
  simp_rw [he]
  simp [mul_ite]

theorem gram_symmetric (σ : Equiv.Perm I) (s : I→R)
    (hσ : Function.Involutive σ) (hs : ∀ i,s (σ i)=s i) : (gram σ s).transpose=gram σ s := by
  ext i j
  by_cases h : j=σ i
  · subst j
    simp [gram,hσ i,hs i]
  · have h' : i≠σ j := by
      intro he
      apply h
      simpa only [hσ j] using (congrArg σ he).symm
    simp [gram,h,h']

end SymmetricSubgroupAsymptotics.CFSGWeightedPermutationGram
