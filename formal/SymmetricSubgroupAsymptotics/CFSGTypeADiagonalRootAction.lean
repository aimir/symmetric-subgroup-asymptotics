import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! Literal diagonal conjugation and commuting monomial-torus
conjugates, used to extract the first root of the actual generating pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeADiagonalRootAction
open Matrix CFSGTypeAElementaryMatrices CFSGTypeAMonomialMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

theorem diagonal_mul_transvection (D : n→F) {i j : n} (hij : i≠j)
    (a : F) (hd : D j≠0) :
    Matrix.diagonal D*Matrix.transvection i j a=
      Matrix.transvection i j (D i*a/D j)*Matrix.diagonal D := by
  ext r s
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.transvection,
    Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
  by_cases hrs : r=s
  · subst s
    by_cases hri : r=i <;> by_cases hrj : r=j <;> simp_all [eq_comm]
  · by_cases hri : r=i <;> by_cases hsj : s=j <;> simp_all [eq_comm]

theorem diagonal_conjugation (h : SL (n:=n) (F:=F)) (D : n→F)
    (hh : h.val=Matrix.diagonal D) {i j : n} (hij : i≠j)
    (a : F) (hd : D j≠0) :
    h*elementary hij a*h⁻¹=elementary hij (D i*a/D j) := by
  have hm : h*elementary hij a=elementary hij (D i*a/D j)*h := by
    apply Subtype.ext
    change h.val*Matrix.transvection i j a=Matrix.transvection i j (D i*a/D j)*h.val
    rw [hh]
    exact diagonal_mul_transvection D hij a hd
  have hc := congrArg (fun X : SL (n:=n) (F:=F) => X*h⁻¹) hm
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hc

/-- Actual monomial conjugation reindexes the torus's diagonal, even
when the monomial lift has nontrivial signed row weights. -/
theorem monomial_conjugate_diagonal
    (W h : SL (n:=n) (F:=F)) (σ : Equiv.Perm n) (d D : n→F)
    (hW : W.val=monomial σ d) (hh : h.val=Matrix.diagonal D) :
    (W*h*W⁻¹).val=Matrix.diagonal (D∘σ) := by
  change W.val*h.val*(W⁻¹).val=Matrix.diagonal (D∘σ)
  rw [hh,hW,monomial_mul_diagonal,←hW,mul_assoc]
  have hi : W.val*(W⁻¹).val=1 := by
    change (W*W⁻¹).val=1
    rw [mul_inv_cancel]
    rfl
  rw [hi,mul_one]

theorem monomial_conjugate_commutes
    (W h : SL (n:=n) (F:=F)) (σ : Equiv.Perm n) (d D : n→F)
    (hW : W.val=monomial σ d) (hh : h.val=Matrix.diagonal D) :
    Commute (W*h*W⁻¹) h := by
  change (W*h*W⁻¹)*h=h*(W*h*W⁻¹)
  apply Subtype.ext
  change (W*h*W⁻¹).val*h.val=h.val*(W*h*W⁻¹).val
  rw [monomial_conjugate_diagonal W h σ d D hW hh,hh,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGTypeADiagonalRootAction
