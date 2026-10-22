import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveDirections

/-! Only finite coordinate inequalities for the six literal positive
root directions. Each of the six checks concerns the eight D4 coordinates;
no field elements or group elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoRootDirectionOrder
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections CFSGGTwoPositivePGroup

def rootEdges (i : Fin 2) : Finset (Index × Index) :=
  if i = 0 then
    {(pos 0, pos 1), (neg 1, neg 0), (pos 2, pos 3),
      (neg 3, neg 2), (pos 2, neg 3), (pos 3, neg 2)}
  else {(pos 1, pos 2), (neg 2, neg 1)}

theorem edge_order (j : Fin 6) (a b : Index) (h : (a, b) ∈ rootEdges (rootNode j)) :
    weight ((directionPermutation j).symm b) < weight ((directionPermutation j).symm a) := by
  revert a b
  fin_cases j <;> decide +kernel

theorem second_order (j : Fin 6) (h : rootNode j = 0) :
    weight ((directionPermutation j).symm (neg 2)) <
      weight ((directionPermutation j).symm (pos 2)) := by
  revert h
  fin_cases j <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGGTwoRootDirectionOrder
