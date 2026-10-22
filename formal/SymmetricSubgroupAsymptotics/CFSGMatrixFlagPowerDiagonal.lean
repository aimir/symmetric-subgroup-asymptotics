import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import Mathlib.Algebra.CharP.Reduced

/-! Defining-characteristic power elements in an actual triangular
matrix flag have diagonal one, directly by injectivity of Frobenius. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {m : ℕ}

theorem flag_diagonal_pow (e : I≃Fin m) (A : Matrix I I K)
    (hA : A.BlockTriangular e) (k : ℕ) (i : I) : (A^k) i i=(A i i)^k := by
  induction k with
  | zero=>simp only [pow_zero,Matrix.one_apply_eq]
  | succ k ih=>rw [pow_succ,upper_diag_mul e (hA.pow k) hA,ih,pow_succ]

theorem diagonal_one_of_prime_power (e : I≃Fin m) (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : Matrix I I K) (hA : A.BlockTriangular e) (k : ℕ) (hk : A^(p^k)=1) (i : I) :
    A i i=1 := by
  have he := congrArg (fun M : Matrix I I K=>M i i) hk
  change (A^(p^k)) i i=(1 : Matrix I I K) i i at he
  rw [flag_diagonal_pow e A hA,Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def,one_pow] using he

end SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
