import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer

/-! One upper-unitriangular matrix with every superdiagonal entry nonzero
recovers every standard flag prefix from its displacement. No Jordan
form, field-size restriction, or collection of sparse tests is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGRegularUpperFlagRecovery
open CFSGMatrixFlagNormalizer
variable {K : Type*} [Field K] {m : ℕ}

theorem recover_prefix (M : Matrix (Fin (m+1)) (Fin (m+1)) K)
    (hupper : M.BlockTriangular id) (hdiag : ∀i,M i i=1)
    (hregular : ∀i : Fin m,M i.castSucc i.succ≠0)
    (k : ℕ) (v : Fin (m+1)→K)
    (hdelta : M*ᵥv-v∈flagPrefix (K:=K) (Equiv.refl _) k) :
    v∈flagPrefix (K:=K) (Equiv.refl _) (k+1) := by
  have hz : ∀t : ℕ,∀j : Fin (m+1),m-j.val=t→k+1≤j.val→v j=0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro j ht hj
      let a : Fin m := ⟨j.val-1,by omega⟩
      have hasucc : a.succ=j := Fin.ext (by dsimp [a]; omega)
      have hane : a.castSucc≠j := by
        intro he
        have hh := congrArg Fin.val he
        dsimp [a] at hh
        omega
      have habove : ∀l : Fin (m+1),j.val<l.val→v l=0 := by
        intro l hlt
        exact ih (m-l.val) (by omega) l rfl (by omega)
      have hrow : ((M-1)*ᵥv) a.castSucc=M a.castSucc j*v j := by
        change (∑l,(M-1) a.castSucc l*v l)=_
        calc
          _=(M-1) a.castSucc j*v j := by
            apply Finset.sum_eq_single j
            · intro l _ hlj
              by_cases hlow : l.val≤a.val
              · by_cases heq : l.val=a.val
                · have he : l=a.castSucc := Fin.ext heq
                  subst l
                  rw [Matrix.sub_apply,hdiag,Matrix.one_apply_eq,sub_self,zero_mul]
                · have hlt : l.val<a.val := by omega
                  have hne : a.castSucc≠l := by
                    intro he
                    have hh := congrArg Fin.val he
                    change a.val=l.val at hh
                    omega
                  have hmzero : M a.castSucc l=0 := hupper (show l<a.castSucc from hlt)
                  rw [Matrix.sub_apply,hmzero,
                    Matrix.one_apply,if_neg hne,sub_self,zero_mul]
              · have hlt : j.val<l.val := by
                  have hljv : l.val≠j.val := fun he=>hlj (Fin.ext he)
                  dsimp [a] at hlow
                  omega
                rw [habove l hlt,mul_zero]
            · intro hn
              exact False.elim (hn (Finset.mem_univ j))
          _=M a.castSucc j*v j := by
            rw [Matrix.sub_apply,Matrix.one_apply,if_neg hane,sub_zero]
      have he : M a.castSucc j*v j=0 := by
        rw [←hrow,Matrix.sub_mulVec,Matrix.one_mulVec]
        exact hdelta a.castSucc (by change k≤a.val; dsimp [a]; omega)
      have hreg : M a.castSucc j≠0 := by rw [←hasucc]; exact hregular a
      exact (mul_eq_zero.mp he).resolve_left hreg
  intro j hj
  exact hz (m-j.val) j rfl hj

end SymmetricSubgroupAsymptotics.CFSGRegularUpperFlagRecovery
