import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Hom.Basic

/-! Extend a literal matrix by an identity block. This is a monoid
homomorphism, so it retains exact word powers. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
variable (R I J : Type*) [CommRing R] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]

def extend : Matrix I I R →* Matrix (I ⊕ J) (I ⊕ J) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

theorem one_sub_zeroExtension (A : Matrix I I R) :
    (1 : Matrix (I ⊕ J) (I ⊕ J) R) - Matrix.fromBlocks A 0 0 0 =
      extend R I J (1 - A) := by
  ext i j
  cases i <;> cases j <;> simp [extend, Matrix.fromBlocks, Matrix.one_apply]

theorem one_add_zeroExtension (A : Matrix I I R) :
    (1 : Matrix (I ⊕ J) (I ⊕ J) R) + Matrix.fromBlocks A 0 0 0 =
      extend R I J (1 + A) := by
  ext i j
  cases i <;> cases j <;> simp [extend, Matrix.fromBlocks, Matrix.one_apply]

theorem scalar_of_extension_scalar (A : Matrix I I R) (c : R)
    (h : extend R I J A = c • (1 : Matrix (I ⊕ J) (I ⊕ J) R)) :
    A = c • (1 : Matrix I I R) := by
  ext i j
  have hh := congrArg (fun M : Matrix (I ⊕ J) (I ⊕ J) R => M (Sum.inl i) (Sum.inl j)) h
  simpa [extend, Matrix.fromBlocks, Matrix.one_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
