import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexParameters

/-! The checked strict-upper coordinate chart covers every actual
alternating matrix, in every characteristic. Diagonal zero is retained
explicitly; skew symmetry alone is not substituted in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingMatrixParameters
open CFSGOrthogonalDIndexParameters
variable {K : Type} [Field K]

def parametersOf (r : ℕ) (B : Matrix (Fin r) (Fin r) K) : Parameters K r :=
  fun x => B ⟨x.2.val, Nat.lt_trans x.2.isLt x.1.isLt⟩ x.1

theorem alternating_parametersOf (r : ℕ) (B : Matrix (Fin r) (Fin r) K)
    (ht : B.transpose = -B) (hd : ∀ i, B i i = 0) :
    alternating (parametersOf r B) = B := by
  ext i j
  change strictUpper (parametersOf r B) i j - strictUpper (parametersOf r B) j i = B i j
  rcases lt_trichotomy i.val j.val with hij | hij | hji
  · rw [strictUpper_apply_lt _ _ _ hij, strictUpper_apply_ge _ _ _ hij.le, sub_zero]
    rfl
  · have he : i = j := Fin.ext hij
    subst j
    rw [strictUpper_apply_ge _ _ _ le_rfl, sub_self, hd]
  · rw [strictUpper_apply_ge _ _ _ hji.le, strictUpper_apply_lt _ _ _ hji, zero_sub]
    have he := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j) ht
    change B j i = -(B i j) at he
    change -(B j i) = B i j
    rw [he, neg_neg]

end SymmetricSubgroupAsymptotics.CFSGAlternatingMatrixParameters
