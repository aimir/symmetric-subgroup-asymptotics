import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnCertificate

/-! Selected column 25 sparse arithmetic. Candidate states do not
establish a theorem until every finite transition below is kernel checked.
The actual original-model action is installed by the shared theorem. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn25
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylColumnCertificate

private def leftStates : Fin 13→Finset (Fin 26) := ![
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25}]

private def rightStates : Fin 57→Finset (Fin 26) := ![
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25},
    {25}]

private theorem left_transition : ∀n : Fin 12,∀j : Fin 26,
    (∑r ∈ leftStates n.castSucc,oneEntry (leftActions n).1 (leftActions n).2 j r)=
      supportValue (leftStates n.succ) j := by decide +kernel

private theorem right_block_0 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 0 n).castSucc,
      oneEntry (rightActions (rightBlock 0 n)).1 (rightActions (rightBlock 0 n)).2 j r)=
      supportValue (rightStates (rightBlock 0 n).succ) j := by decide +kernel

private theorem right_block_1 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 1 n).castSucc,
      oneEntry (rightActions (rightBlock 1 n)).1 (rightActions (rightBlock 1 n)).2 j r)=
      supportValue (rightStates (rightBlock 1 n).succ) j := by decide +kernel

private theorem right_block_2 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 2 n).castSucc,
      oneEntry (rightActions (rightBlock 2 n)).1 (rightActions (rightBlock 2 n)).2 j r)=
      supportValue (rightStates (rightBlock 2 n).succ) j := by decide +kernel

private theorem right_block_3 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 3 n).castSucc,
      oneEntry (rightActions (rightBlock 3 n)).1 (rightActions (rightBlock 3 n)).2 j r)=
      supportValue (rightStates (rightBlock 3 n).succ) j := by decide +kernel

private theorem right_block_4 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 4 n).castSucc,
      oneEntry (rightActions (rightBlock 4 n)).1 (rightActions (rightBlock 4 n)).2 j r)=
      supportValue (rightStates (rightBlock 4 n).succ) j := by decide +kernel

private theorem right_block_5 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 5 n).castSucc,
      oneEntry (rightActions (rightBlock 5 n)).1 (rightActions (rightBlock 5 n)).2 j r)=
      supportValue (rightStates (rightBlock 5 n).succ) j := by decide +kernel

private theorem right_block_6 : ∀n : Fin 8,∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock 6 n).castSucc,
      oneEntry (rightActions (rightBlock 6 n)).1 (rightActions (rightBlock 6 n)).2 j r)=
      supportValue (rightStates (rightBlock 6 n).succ) j := by decide +kernel

private theorem right_blocks (b : Fin 7) (n : Fin 8) : ∀j : Fin 26,
    (∑r ∈ rightStates (rightBlock b n).castSucc,
      oneEntry (rightActions (rightBlock b n)).1 (rightActions (rightBlock b n)).2 j r)=
      supportValue (rightStates (rightBlock b n).succ) j := by
  fin_cases b
  · exact right_block_0 n
  · exact right_block_1 n
  · exact right_block_2 n
  · exact right_block_3 n
  · exact right_block_4 n
  · exact right_block_5 n
  · exact right_block_6 n

def certificate : ColumnCertificate 25 where
  leftStates := leftStates
  rightStates := rightStates
  leftInitial := by decide +kernel
  rightInitial := by decide +kernel
  finalAgreement := by decide +kernel
  leftTransition := left_transition
  rightTransition := right_transitions_of_blocks rightStates right_blocks

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn25
