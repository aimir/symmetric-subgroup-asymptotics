import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Tactic.FinCases

/-! Literal coordinates for adjoining the LAST hyperbolic pair to a
split D space. The retained smaller space uses castSucc on both halves. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockCoordinates
open CFSGOrthogonalDSerreMatrices

def blockIndex (n : ℕ) : Index n → Index (n + 1)
  | .inl i => .inl i.castSucc
  | .inr i => .inr i.castSucc

private def joinIndex (n : ℕ) : Index n ⊕ Fin 2 → Index (n + 1)
  | .inl i => blockIndex n i
  | .inr j => if j = 0 then .inl (Fin.last n) else .inr (Fin.last n)

private def splitIndex (n : ℕ) : Index (n + 1) → Index n ⊕ Fin 2
  | .inl i => Fin.lastCases (.inr 0) (fun j => .inl (.inl j)) i
  | .inr i => Fin.lastCases (.inr 1) (fun j => .inl (.inr j)) i

def blockEquiv (n : ℕ) : Index n ⊕ Fin 2 ≃ Index (n + 1) where
  toFun := joinIndex n
  invFun := splitIndex n
  left_inv x := by
    rcases x with (i | i) | j
    · simp [joinIndex, blockIndex, splitIndex]
    · simp [joinIndex, blockIndex, splitIndex]
    · fin_cases j <;> simp [joinIndex, splitIndex]
  right_inv x := by
    rcases x with i | i
    · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [joinIndex, splitIndex, blockIndex]
    · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [joinIndex, splitIndex, blockIndex]

@[simp] theorem blockEquiv_inl (n : ℕ) (i : Index n) :
    blockEquiv n (Sum.inl i) = blockIndex n i := rfl

@[simp] theorem blockEquiv_zero (n : ℕ) :
    blockEquiv n (Sum.inr 0) = Sum.inl (Fin.last n) := rfl

@[simp] theorem blockEquiv_one (n : ℕ) :
    blockEquiv n (Sum.inr 1) = Sum.inr (Fin.last n) := rfl

@[simp] theorem blockEquiv_symm_blockIndex (n : ℕ) (i : Index n) :
    (blockEquiv n).symm (blockIndex n i) = Sum.inl i :=
  (blockEquiv n).symm_apply_apply (Sum.inl i)

@[simp] theorem blockEquiv_symm_positive_last (n : ℕ) :
    (blockEquiv n).symm (Sum.inl (Fin.last n)) = Sum.inr 0 :=
  (blockEquiv n).symm_apply_apply (Sum.inr 0)

@[simp] theorem blockEquiv_symm_negative_last (n : ℕ) :
    (blockEquiv n).symm (Sum.inr (Fin.last n)) = Sum.inr 1 :=
  (blockEquiv n).symm_apply_apply (Sum.inr 1)

theorem blockIndex_injective (n : ℕ) : Function.Injective (blockIndex n) := by
  intro i j hij
  have h : blockEquiv n (Sum.inl i) = blockEquiv n (Sum.inl j) := hij
  exact Sum.inl.inj ((blockEquiv n).injective h)

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockCoordinates
