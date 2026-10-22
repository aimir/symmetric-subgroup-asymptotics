import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import Mathlib.Tactic.FinCases

/-! Exact original D tail coordinates, omitting only the first
hyperbolic pair. No low-rank model identification is involved. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices

def tailIndex (n : ℕ) : Index n → Index (n + 1)
  | .inl i => .inl i.succ
  | .inr i => .inr i.succ

private def joinIndex (n : ℕ) : Index n ⊕ Fin 2 → Index (n + 1)
  | .inl x => tailIndex n x
  | .inr i => if i = 0 then .inl 0 else .inr 0

private def splitIndex (n : ℕ) : Index (n + 1) → Index n ⊕ Fin 2
  | .inl i => Fin.cases (.inr 0) (fun j => .inl (.inl j)) i
  | .inr i => Fin.cases (.inr 1) (fun j => .inl (.inr j)) i

def tailEquiv (n : ℕ) : Index n ⊕ Fin 2 ≃ Index (n + 1) where
  toFun := joinIndex n
  invFun := splitIndex n
  left_inv := by
    intro x
    rcases x with (i | i) | j
    · rfl
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    intro x
    rcases x with i | i
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem tailEquiv_inl (n : ℕ) (i : Index n) :
    tailEquiv n (Sum.inl i) = tailIndex n i := rfl
@[simp] theorem tailEquiv_zero (n : ℕ) : tailEquiv n (Sum.inr 0) = Sum.inl 0 := rfl
@[simp] theorem tailEquiv_one (n : ℕ) : tailEquiv n (Sum.inr 1) = Sum.inr 0 := rfl

@[simp] theorem tailEquiv_symm_tailIndex (n : ℕ) (i : Index n) :
    (tailEquiv n).symm (tailIndex n i) = Sum.inl i :=
  (tailEquiv n).symm_apply_apply (Sum.inl i)
@[simp] theorem tailEquiv_symm_positive_zero (n : ℕ) :
    (tailEquiv n).symm (Sum.inl 0) = Sum.inr 0 :=
  (tailEquiv n).symm_apply_apply (Sum.inr 0)
@[simp] theorem tailEquiv_symm_negative_zero (n : ℕ) :
    (tailEquiv n).symm (Sum.inr 0) = Sum.inr 1 :=
  (tailEquiv n).symm_apply_apply (Sum.inr 1)

theorem tailIndex_injective (n : ℕ) : Function.Injective (tailIndex n) := by
  intro i j hij
  have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inl j) := hij
  exact Sum.inl.inj ((tailEquiv n).injective hh)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
