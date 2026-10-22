import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup
import Mathlib.Tactic.FinCases

/-! The original B tail coordinates plus the first hyperbolic pair are
an explicit reindexing of the next-rank original natural space. The
middle coordinate belongs to the tail and is never discarded. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSerreMatrices

def tailIndex (n : ℕ) : Index n → Index (n + 1)
  | .inl (.inl i) => pos (n + 1) i.succ
  | .inl (.inr i) => neg (n + 1) i.succ
  | .inr _ => middle (n + 1)

private def joinIndex (n : ℕ) : Index n ⊕ Fin 2 → Index (n + 1)
  | .inl x => tailIndex n x
  | .inr i => if i = 0 then pos (n + 1) 0 else neg (n + 1) 0

private def splitIndex (n : ℕ) : Index (n + 1) → Index n ⊕ Fin 2
  | .inl (.inl i) => Fin.cases (.inr 0) (fun j => .inl (pos n j)) i
  | .inl (.inr i) => Fin.cases (.inr 1) (fun j => .inl (neg n j)) i
  | .inr _ => .inl (middle n)

def tailEquiv (n : ℕ) : Index n ⊕ Fin 2 ≃ Index (n + 1) where
  toFun := joinIndex n
  invFun := splitIndex n
  left_inv := by
    intro x
    rcases x with ((i | i) | ⟨⟩) | j
    · rfl
    · rfl
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    intro x
    rcases x with (i | i) | ⟨⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    · refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    · rfl

@[simp] theorem tailEquiv_inl (n : ℕ) (i : Index n) :
    tailEquiv n (Sum.inl i) = tailIndex n i := rfl

@[simp] theorem tailEquiv_zero (n : ℕ) : tailEquiv n (Sum.inr 0) = pos (n + 1) 0 := rfl
@[simp] theorem tailEquiv_one (n : ℕ) : tailEquiv n (Sum.inr 1) = neg (n + 1) 0 := rfl

@[simp] theorem tailEquiv_symm_tailIndex (n : ℕ) (i : Index n) :
    (tailEquiv n).symm (tailIndex n i) = Sum.inl i :=
  (tailEquiv n).symm_apply_apply (Sum.inl i)

@[simp] theorem tailEquiv_symm_pos_zero (n : ℕ) :
    (tailEquiv n).symm (pos (n + 1) 0) = Sum.inr 0 :=
  (tailEquiv n).symm_apply_apply (Sum.inr 0)

@[simp] theorem tailEquiv_symm_neg_zero (n : ℕ) :
    (tailEquiv n).symm (neg (n + 1) 0) = Sum.inr 1 :=
  (tailEquiv n).symm_apply_apply (Sum.inr 1)

theorem tailIndex_injective (n : ℕ) : Function.Injective (tailIndex n) := by
  intro i j hij
  have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inl j) := hij
  exact Sum.inl.inj ((tailEquiv n).injective hh)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
