import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! Exact elementary-root transport by actual monomial matrices. Every
nonzero row weight and original point permutation is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction
open Matrix CFSGTypeAElementaryMatrices CFSGTypeAMonomialMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

theorem monomial_mul_transvection (σ : Equiv.Perm n) (d : n→F)
    (i j : n) (a : F) (hd : d (σ.symm j)≠0) :
    monomial σ d*Matrix.transvection i j a=
      Matrix.transvection (σ.symm i) (σ.symm j) (d (σ.symm i)*a/d (σ.symm j))*monomial σ d := by
  simp only [Matrix.transvection,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,Matrix.one_mul]
  congr 1
  ext r s
  by_cases hr : r=σ.symm i <;> by_cases hs : s=j
  · subst r
    subst s
    rw [Matrix.mul_single_apply_same,Matrix.single_mul_apply_same]
    simp only [monomial_apply,σ.apply_symm_apply,ite_true]
    field_simp [hd] <;> ring
  · subst r
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hs,Matrix.single_mul_apply_same]
    simp [monomial_apply,Ne.symm hs]
  · subst s
    rw [Matrix.mul_single_apply_same,Matrix.single_mul_apply_of_ne _ _ _ _ _ hr]
    have hσr : σ r≠i := by
      intro he
      apply hr
      simpa only [σ.symm_apply_apply] using congrArg σ.symm he
    simp [monomial_apply,hσr]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hs,
      Matrix.single_mul_apply_of_ne _ _ _ _ _ hr]

/-- Exact point and scalar transport inside the original SL group. -/
theorem monomial_conjugation (W : SL (n:=n) (F:=F)) (σ : Equiv.Perm n) (d : n→F)
    (hW : W.val=monomial σ d) {i j : n} (hij : i≠j) (a : F)
    (hd : d (σ.symm j)≠0) :
    W*elementary hij a*W⁻¹=
      elementary (σ.symm.injective.ne hij) (d (σ.symm i)*a/d (σ.symm j)) := by
  have hm : W*elementary hij a=
      elementary (σ.symm.injective.ne hij) (d (σ.symm i)*a/d (σ.symm j))*W := by
    apply Subtype.ext
    change W.val*Matrix.transvection i j a=
      Matrix.transvection (σ.symm i) (σ.symm j) (d (σ.symm i)*a/d (σ.symm j))*W.val
    rw [hW]
    exact monomial_mul_transvection σ d i j a hd
  have hc := congrArg (fun X : SL (n:=n) (F:=F) => X*W⁻¹) hm
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hc

/-- A full root group is carried to a full root group, with no assumption
that its original coefficient is preserved by the monomial weights. -/
theorem full_root_transfer (H : Subgroup (SL (n:=n) (F:=F)))
    (W : SL (n:=n) (F:=F)) (hHW : W∈H) (σ : Equiv.Perm n) (d : n→F)
    (hW : W.val=monomial σ d) (hd : ∀ k,d k≠0)
    {i j : n} (hij : i≠j) (hRoot : ∀ a : F,elementary hij a∈H) :
    ∀ b : F,elementary (σ.symm.injective.ne hij) b∈H := by
  intro b
  let a := d (σ.symm j)*b/d (σ.symm i)
  have hm := H.mul_mem (H.mul_mem hHW (hRoot a)) (H.inv_mem hHW)
  rw [monomial_conjugation W σ d hW hij a (hd _)] at hm
  have he : d (σ.symm i)*a/d (σ.symm j)=b := by
    dsimp [a]
    field_simp [hd (σ.symm i),hd (σ.symm j)]
  simpa only [he] using hm

end SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction
