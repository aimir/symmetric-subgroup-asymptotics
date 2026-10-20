import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_000
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_001
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_002
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_003
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_004
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_005
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_006
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_007
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_008
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_009
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_010
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_011
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_012
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_013
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_014
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_015
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_016
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_017
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotEdges046_018

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry046
local instance pilotAggregateGroup : Group Source := BinaryTopSource046.group

private def child (i : Fin 19) : Source → Fin 19 :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then child0 else child1) else (if i.val < 3 then child2 else child3)) else (if i.val < 6 then (if i.val < 5 then child4 else child5) else (if i.val < 7 then child6 else (if i.val < 8 then child7 else child8)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then child9 else child10) else (if i.val < 12 then child11 else (if i.val < 13 then child12 else child13))) else (if i.val < 16 then (if i.val < 15 then child14 else child15) else (if i.val < 17 then child16 else (if i.val < 18 then child17 else child18)))))

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
    · exact fun x hx => (edges11 x hx).1
    · exact fun x hx => (edges12 x hx).1
    · exact fun x hx => (edges13 x hx).1
    · exact fun x hx => (edges14 x hx).1
    · exact fun x hx => (edges15 x hx).1
    · exact fun x hx => (edges16 x hx).1
    · exact fun x hx => (edges17 x hx).1
    · exact fun x hx => (edges18 x hx).1
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
    · exact fun x hx => (edges11 x hx).2.1
    · exact fun x hx => (edges12 x hx).2.1
    · exact fun x hx => (edges13 x hx).2.1
    · exact fun x hx => (edges14 x hx).2.1
    · exact fun x hx => (edges15 x hx).2.1
    · exact fun x hx => (edges16 x hx).2.1
    · exact fun x hx => (edges17 x hx).2.1
    · exact fun x hx => (edges18 x hx).2.1
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
    · exact fun x hx => (edges11 x hx).2.2
    · exact fun x hx => (edges12 x hx).2.2
    · exact fun x hx => (edges13 x hx).2.2
    · exact fun x hx => (edges14 x hx).2.2
    · exact fun x hx => (edges15 x hx).2.2
    · exact fun x hx => (edges16 x hx).2.2
    · exact fun x hx => (edges17 x hx).2.2
    · exact fun x hx => (edges18 x hx).2.2

theorem isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := 4) (by rw [Nat.card_eq_fintype_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel=N := registry.complete isPGroup N

/-- Completeness on the original literal permutation top, without an
abstract isomorphism replacing its action. -/
def originalStates (i : Fin 19) : BinaryTopKernelData
    (Subgroup.closure (Set.range BinaryTopSource046.generators)) :=
  (states i).transport BinaryTopSource046.originalEquiv

theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range BinaryTopSource046.generators))) [N.Normal] :
    ∃ i, (originalStates i).kernel=N := by
  obtain ⟨i,hi⟩ := registry.complete_map_of_equiv isPGroup BinaryTopSource046.originalEquiv N
  exact ⟨i,((states i).transport_kernel BinaryTopSource046.originalEquiv).trans hi⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry046
