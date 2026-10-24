import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnPilot

/-! A reusable sparse certificate for an arbitrary norm26 basis column.
All data and transition assertions are over F2. Group-word conclusions
require the separately proved actual-action installer. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnCertificate
open CFSGFFourE6MiddleWeylColumnPilot

structure ColumnCertificate (k : Fin 26) where
  leftStates : Fin 13→Finset (Fin 26)
  rightStates : Fin 57→Finset (Fin 26)
  leftInitial : leftStates 0={k}
  rightInitial : rightStates 0={k}
  finalAgreement : leftStates (Fin.last 12)=rightStates (Fin.last 56)
  leftTransition : ∀n : Fin 12,∀j : Fin 26,
    (∑r ∈ leftStates n.castSucc,oneEntry (leftActions n).1 (leftActions n).2 j r)=
      supportValue (leftStates n.succ) j
  rightTransition : ∀n : Fin 56,∀j : Fin 26,
    (∑r ∈ rightStates n.castSucc,oneEntry (rightActions n).1 (rightActions n).2 j r)=
      supportValue (rightStates n.succ) j

theorem right_transitions_of_blocks (states : Fin 57→Finset (Fin 26))
    (hblocks : ∀b : Fin 7,∀n : Fin 8,∀j : Fin 26,
      (∑r ∈ states (rightBlock b n).castSucc,
        oneEntry (rightActions (rightBlock b n)).1 (rightActions (rightBlock b n)).2 j r)=
        supportValue (states (rightBlock b n).succ) j) :
    ∀n : Fin 56,∀j : Fin 26,
      (∑r ∈ states n.castSucc,oneEntry (rightActions n).1 (rightActions n).2 j r)=
        supportValue (states n.succ) j := by
  intro n
  let b : Fin 7 := ⟨n.val/8,by omega⟩
  let k : Fin 8 := ⟨n.val%8,Nat.mod_lt _ (by decide)⟩
  have he : rightBlock b k=n := by
    apply Fin.ext
    dsimp only [rightBlock,b,k]
    omega
  rw [←he]
  exact hblocks b k

private theorem zero_blocks (b : Fin 7) (n : Fin 8) : ∀j : Fin 26,
    (∑r ∈ rightSupports (rightBlock b n).castSucc,
      oneEntry (rightActions (rightBlock b n)).1 (rightActions (rightBlock b n)).2 j r)=
      supportValue (rightSupports (rightBlock b n).succ) j := by
  fin_cases b
  · exact right_column_transitions_0 n
  · exact right_column_transitions_1 n
  · exact right_column_transitions_2 n
  · exact right_column_transitions_3 n
  · exact right_column_transitions_4 n
  · exact right_column_transitions_5 n
  · exact right_column_transitions_6 n

def zeroCertificate : ColumnCertificate 0 where
  leftStates := leftSupports
  rightStates := rightSupports
  leftInitial := initial_and_final_supports.1
  rightInitial := initial_and_final_supports.2.1
  finalAgreement := by
    change leftSupports (12 : Fin 13)=rightSupports (56 : Fin 57)
    exact initial_and_final_supports.2.2.1.trans initial_and_final_supports.2.2.2.symm
  leftTransition := left_column_transitions
  rightTransition := right_transitions_of_blocks rightSupports zero_blocks

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnCertificate
