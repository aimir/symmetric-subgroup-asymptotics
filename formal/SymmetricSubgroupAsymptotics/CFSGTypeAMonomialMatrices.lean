import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.GroupTheory.Perm.Sign

/-! Literal monomial matrices and determinant-one lifts of point
permutations. Their diagonal conjugation keeps the actual point chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

def monomial (σ : Equiv.Perm n) (d : n→F) : Matrix n n F :=
  Matrix.diagonal d*(1 : Matrix n n F).submatrix σ id

@[simp] theorem monomial_apply (σ : Equiv.Perm n) (d : n→F) (i j : n) :
    monomial σ d i j=if σ i=j then d i else 0 := by
  simp [monomial,Matrix.diagonal_mul,Matrix.submatrix_apply,Matrix.one_apply,mul_ite]

/-- The row weights cancel from the diagonal commutation relation; the
original point permutation controls the diagonal coordinates exactly. -/
theorem monomial_mul_diagonal (σ : Equiv.Perm n) (d D : n→F) :
    monomial σ d*Matrix.diagonal D=Matrix.diagonal (D∘σ)*monomial σ d := by
  ext i j
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,monomial_apply,Function.comp_apply]
  by_cases h : σ i=j
  · subst j
    simp [mul_comm]
  · simp [h]

/-- The sign is placed at one original coordinate, giving an actual SL
lift of any finite point permutation. No abstract Weyl-group model or
scalar-quotient identification is used. -/
def signedPermutation (b : n) (σ : Equiv.Perm n) : Matrix.SpecialLinearGroup n F :=
  ⟨monomial σ (fun k => if k=b then (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : F) else 1),by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs|hs <;>
      simp [monomial,Matrix.det_mul,Matrix.det_diagonal,Matrix.det_permute,
        Fintype.prod_ite_eq',hs]⟩

@[simp] theorem signedPermutation_coe (b : n) (σ : Equiv.Perm n) :
    (signedPermutation (F:=F) b σ).val=
      monomial σ (fun k => if k=b then (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : F) else 1) := rfl

end SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices
