import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_000
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_001
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_002
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_003
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_004
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_005
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_006
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_007
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_008
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_009
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges056_010

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry056
local instance pilotAggregateGroup : Group Source := BinaryTopSource056.group

private def child (i : Fin 11) : Source → Fin 11 :=
  (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then child0 else child1) else (if i.val < 3 then child2 else (if i.val < 4 then child3 else child4))) else (if i.val < 8 then (if i.val < 6 then child5 else (if i.val < 7 then child6 else child7)) else (if i.val < 9 then child8 else (if i.val < 10 then child9 else child10))))

def registry : BinaryTopNormalRegistry generators states where
  bottom := 0
  bottom_mask := by decide +kernel
  child := child
  parent_mem := by
    intro i
    fin_cases i
    · exact fun x hx => (edges0 x hx).1
    · exact fun x hx => (edges1 x hx).1
    · exact fun x hx => (edges2 x hx).1
    · exact fun x hx => (edges3 x hx).1
    · exact fun x hx => (edges4 x hx).1
    · exact fun x hx => (edges5 x hx).1
    · exact fun x hx => (edges6 x hx).1
    · exact fun x hx => (edges7 x hx).1
    · exact fun x hx => (edges8 x hx).1
    · exact fun x hx => (edges9 x hx).1
    · exact fun x hx => (edges10 x hx).1
  lift_mem := by
    intro i
    fin_cases i
    · exact fun x hx => (edges0 x hx).2.1
    · exact fun x hx => (edges1 x hx).2.1
    · exact fun x hx => (edges2 x hx).2.1
    · exact fun x hx => (edges3 x hx).2.1
    · exact fun x hx => (edges4 x hx).2.1
    · exact fun x hx => (edges5 x hx).2.1
    · exact fun x hx => (edges6 x hx).2.1
    · exact fun x hx => (edges7 x hx).2.1
    · exact fun x hx => (edges8 x hx).2.1
    · exact fun x hx => (edges9 x hx).2.1
    · exact fun x hx => (edges10 x hx).2.1
  child_size := by
    intro i
    fin_cases i
    · exact fun x hx => (edges0 x hx).2.2
    · exact fun x hx => (edges1 x hx).2.2
    · exact fun x hx => (edges2 x hx).2.2
    · exact fun x hx => (edges3 x hx).2.2
    · exact fun x hx => (edges4 x hx).2.2
    · exact fun x hx => (edges5 x hx).2.2
    · exact fun x hx => (edges6 x hx).2.2
    · exact fun x hx => (edges7 x hx).2.2
    · exact fun x hx => (edges8 x hx).2.2
    · exact fun x hx => (edges9 x hx).2.2
    · exact fun x hx => (edges10 x hx).2.2

theorem isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := 4) (by rw [Nat.card_eq_fintype_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel=N := registry.complete isPGroup N

/-- Completeness on the original literal permutation top, without an
abstract isomorphism replacing its action. -/
def originalStates (i : Fin 11) : BinaryTopKernelData
    (Subgroup.closure (Set.range BinaryTopSource056.generators)) :=
  (states i).transport BinaryTopSource056.originalEquiv

theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range BinaryTopSource056.generators))) [N.Normal] :
    ∃ i, (originalStates i).kernel=N := by
  obtain ⟨i,hi⟩ := registry.complete_map_of_equiv isPGroup BinaryTopSource056.originalEquiv N
  exact ⟨i,((states i).transport_kernel BinaryTopSource056.originalEquiv).trans hi⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry056
