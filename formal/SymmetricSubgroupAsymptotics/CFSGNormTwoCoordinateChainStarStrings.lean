import SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! Exact adjacent root strings in the selected exceptional A-chain star.
The actual coordinate simple reflection swaps the adjacent two star
roots and fixes all others. These are integral root-label equalities;
parameter signs are supplied by the proved Weyl-word transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalChainStarData CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoGeckWeylWordDegree
variable {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (C : ChainStar A n)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem simple_pair (j : Fin n) (k : Fin (n+1)) :
    integerPairing A (C.root k).val.val (s₀ (C.step j) : Roots A).val=
      if k=j.castSucc then -1 else if k=j.succ then 1 else 0 := by
  change integerPairing A (C.row k) (Pi.single (C.step j) 1)=_
  exact C.simple_pair j k

theorem raised_root (j : Fin n)
    (hpair : integerPairing A (C.root j.castSucc).val.val
      (s₀ (C.step j) : Roots A).val= -1) :
    raisedRoot A hd hs hp ho (C.root j.castSucc).val (C.step j) hpair=(C.root j.succ).val := by
  apply Subtype.ext
  change C.row j.castSucc+Pi.single (C.step j) 1=C.row j.succ
  exact (C.successor j).symm

theorem reflected_root (j : Fin n) (k : Fin (n+1)) :
    wordRoot A hs hp b₀ s₀ [C.step j] (C.root k).val=
      (C.root (Equiv.swap j.castSucc j.succ k)).val := by
  apply Subtype.ext
  change C.row k-integerPairing A (C.row k) (Pi.single (C.step j) 1) •
    (Pi.single (C.step j) 1)=C.row (Equiv.swap j.castSucc j.succ k)
  rw [C.simple_pair]
  by_cases hleft : k=j.castSucc
  · subst k
    rw [if_pos rfl,Equiv.swap_apply_left,neg_one_smul,sub_neg_eq_add]
    exact (C.successor j).symm
  · rw [if_neg hleft]
    by_cases hright : k=j.succ
    · subst k
      rw [if_pos rfl,Equiv.swap_apply_right,one_smul,C.successor]
      exact add_sub_cancel_right _ _
    · rw [if_neg hright,zero_smul,sub_zero,Equiv.swap_apply_of_ne_of_ne hleft hright]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarStrings
