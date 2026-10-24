import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoefficientPilot
import Mathlib.Data.ZMod.Basic

/-! Selected column-zero arithmetic pilot for the actual norm26 middle
Weyl word. Every sparse transition is checked modulo two; this finite
certificate alone makes no assertion about a group representation. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnPilot
open CFSGFFourE6NormQuotientCoefficientPilot

def columnLabels : Fin 26→RawIndex := ![
    Sum.inl 0,
    Sum.inl 2,
    Sum.inr ![-1,-1,-2,-2,-1,-1],
    Sum.inr ![-1,-1,-2,-2,-1,0],
    Sum.inr ![-1,-1,-1,-2,-1,0],
    Sum.inr ![-1,-1,-1,-1,-1,0],
    Sum.inr ![-1,-1,-1,-1,0,0],
    Sum.inr ![-1,0,-1,-1,-1,0],
    Sum.inr ![-1,0,-1,-1,0,0],
    Sum.inr ![-1,0,-1,0,0,0],
    Sum.inr ![-1,0,0,0,0,0],
    Sum.inr ![0,-1,-1,-1,0,0],
    Sum.inr ![0,0,-1,-1,0,0],
    Sum.inr ![0,0,-1,0,0,0],
    Sum.inr ![0,0,0,0,0,1],
    Sum.inr ![0,0,0,0,1,0],
    Sum.inr ![0,0,0,0,1,1],
    Sum.inr ![0,0,0,1,1,0],
    Sum.inr ![0,0,0,1,1,1],
    Sum.inr ![0,0,1,1,1,1],
    Sum.inr ![0,1,0,1,1,0],
    Sum.inr ![0,1,0,1,1,1],
    Sum.inr ![0,1,1,1,1,1],
    Sum.inr ![0,1,1,2,1,1],
    Sum.inr ![0,1,1,2,2,1],
    Sum.inr ![1,1,1,2,2,1]]

def negativeLabel : RawIndex→RawIndex
  | .inl i=>.inl i
  | .inr r=>.inr (fun i=> -r (CFSG.Models.e6Twist i))

def normEntry (T : RawIndex→RawIndex→ℤ) (r s : RawIndex) : ℤ :=
  T r s+T r (partnerIndex s)

def oneEntry (neg : Bool) (axis : Fin 4) (j k : Fin 26) : ZMod 2 :=
  let r := if neg then negativeLabel (columnLabels j) else columnLabels j
  let s := if neg then negativeLabel (columnLabels k) else columnLabels k
  (if j=k then 1 else 0)+
    (normEntry (if axis=1 then shortFirst else longFirst) r s : ZMod 2)+
    (normEntry (if axis=1 then shortSecond else longSecond) r s : ZMod 2)

def supportValue (s : Finset (Fin 26)) (j : Fin 26) : ZMod 2 := if j∈s then 1 else 0

def leftActions : Fin 12→Bool×Fin 4 := ![
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1)]

def leftSupports : Fin 13→Finset (Fin 26) := ![
    {0},
    {0},
    {0},
    {0},
    {0,15},
    {0,1,15},
    {0,1},
    {0,1},
    {0,1},
    {0,1},
    {0,1,15},
    {0,15},
    {0}]

theorem left_column_transitions : ∀n : Fin 12,∀j : Fin 26,
    (∑k ∈ leftSupports n.castSucc,
      oneEntry (leftActions n).1 (leftActions n).2 j k)=
      supportValue (leftSupports n.succ) j := by decide +kernel

def rightActions : Fin 56→Bool×Fin 4 := ![
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,2),
    (false,1),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (false,2),
    (true,2),
    (false,2),
    (false,1),
    (true,1),
    (false,1),
    (false,2),
    (false,1),
    (true,1),
    (false,1)]

def rightSupports : Fin 57→Finset (Fin 26) := ![
    {0},
    {0},
    {0},
    {0},
    {0,15},
    {0,15,17},
    {0,17},
    {0,17},
    {0,17},
    {0,15,17},
    {0,17},
    {0,13,17},
    {0,1,13,17},
    {0,1,13,17},
    {0,1,12,13,15,17},
    {0,1,12,15},
    {0,1,12},
    {0,1,12,13},
    {0,12,13},
    {0,12},
    {0,12},
    {0,12,13},
    {0,1,12,13},
    {0,1,12},
    {0,1,12,15},
    {0,1,12,13,15,17},
    {0,12,13,15,17},
    {0,1,12,13,15,17},
    {0,12,13,15,17},
    {0,12,15},
    {0,12},
    {0,12,13},
    {0,13},
    {0,13},
    {0,1,13},
    {0,1},
    {0,1,15},
    {0,1,15,17},
    {0,1,17},
    {0,1,17},
    {0,1,15,17},
    {0,15,17},
    {0,17},
    {0,17},
    {0,15,17},
    {0,15},
    {0},
    {0},
    {0},
    {0},
    {0,15},
    {0,1,15},
    {0,1},
    {0,1},
    {0,1,15},
    {0,15},
    {0}]

def rightBlock (block : Fin 7) (n : Fin 8) : Fin 56 :=
  ⟨8*block.val+n.val,by omega⟩

theorem right_column_transitions_0 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 0 n).castSucc,
      oneEntry (rightActions (rightBlock 0 n)).1 (rightActions (rightBlock 0 n)).2 j k)=
      supportValue (rightSupports (rightBlock 0 n).succ) j := by decide +kernel

theorem right_column_transitions_1 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 1 n).castSucc,
      oneEntry (rightActions (rightBlock 1 n)).1 (rightActions (rightBlock 1 n)).2 j k)=
      supportValue (rightSupports (rightBlock 1 n).succ) j := by decide +kernel

theorem right_column_transitions_2 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 2 n).castSucc,
      oneEntry (rightActions (rightBlock 2 n)).1 (rightActions (rightBlock 2 n)).2 j k)=
      supportValue (rightSupports (rightBlock 2 n).succ) j := by decide +kernel

theorem right_column_transitions_3 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 3 n).castSucc,
      oneEntry (rightActions (rightBlock 3 n)).1 (rightActions (rightBlock 3 n)).2 j k)=
      supportValue (rightSupports (rightBlock 3 n).succ) j := by decide +kernel

theorem right_column_transitions_4 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 4 n).castSucc,
      oneEntry (rightActions (rightBlock 4 n)).1 (rightActions (rightBlock 4 n)).2 j k)=
      supportValue (rightSupports (rightBlock 4 n).succ) j := by decide +kernel

theorem right_column_transitions_5 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 5 n).castSucc,
      oneEntry (rightActions (rightBlock 5 n)).1 (rightActions (rightBlock 5 n)).2 j k)=
      supportValue (rightSupports (rightBlock 5 n).succ) j := by decide +kernel

theorem right_column_transitions_6 : ∀n : Fin 8,∀j : Fin 26,
    (∑k ∈ rightSupports (rightBlock 6 n).castSucc,
      oneEntry (rightActions (rightBlock 6 n)).1 (rightActions (rightBlock 6 n)).2 j k)=
      supportValue (rightSupports (rightBlock 6 n).succ) j := by decide +kernel

theorem initial_and_final_supports :
    leftSupports 0={0} ∧ rightSupports 0={0} ∧
      leftSupports 12={0} ∧ rightSupports 56={0} := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnPilot
