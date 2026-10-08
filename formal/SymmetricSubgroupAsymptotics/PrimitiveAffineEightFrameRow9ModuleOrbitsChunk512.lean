import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsData

/-! Selected row 9 vector orbits 512–534. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512

abbrev Source := PrimitiveAffineEightFrameRow9ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group

def embed (i : Fin 23) : Fin 535 :=
  ⟨512 + i.val, by omega⟩

theorem minimal : ∀ i : Fin 23, ∀ g,
    binaryVectorMask (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i)) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow9ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))) :=
  (Fin.addCases (m := 11) (n := 12) (by native_decide) (by native_decide))

theorem stabilizer_card : ∀ i : Fin 23,
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
      (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))) =
        PrimitiveAffineEightFrameRow9ModuleOrbitsData.stabilizerCard (embed i) := by
  intro i
  letI : DecidablePred (fun g : Source ↦
      g ∈ representationVectorStabilizer
        PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))) :=
    fun g ↦ decidable_of_iff
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i)) = PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))
      Iff.rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> native_decide

private def relationWords (i : Fin 23) : List Source :=
  (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4,6]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4,6]]) else (if i.val < 3 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1]] else (if i.val < 4 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3]]))) else (if i.val < 8 then (if i.val < 6 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4]] else (if i.val < 7 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1]])) else (if i.val < 9 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,5]] else (if i.val < 10 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0]])))) else (if i.val < 17 then (if i.val < 14 then (if i.val < 12 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0]] else (if i.val < 13 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4]])) else (if i.val < 15 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,2]] else (if i.val < 16 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2,6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [3,6]]))) else (if i.val < 20 then (if i.val < 18 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2,3]] else (if i.val < 19 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1]])) else (if i.val < 21 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4]] else (if i.val < 22 then [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord [0,1]])))))

theorem orbit_mem_chart : ∀ i : Fin 23,
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic (embed i)))).2.inclusion
        ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic (embed i)))).2.coordinates
          (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))) =
      PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i) :=
  (Fin.addCases (m := 11) (n := 12) (by native_decide) (by native_decide))

theorem relation_eq : ∀ i : Fin 23,
    PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic (embed i)) =
      ((relationWords i).map (fun g ↦
        PrimitiveAffineEightFrameRow9ModuleRepresentation.representation g
          (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i)))).sum :=
  (Fin.addCases (m := 11) (n := 12) (by native_decide) (by native_decide))

theorem canonical_mem_orbit_span (i : Fin 23) :
    PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic (embed i)) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i)) := by
  rw [relation_eq i]
  apply (binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative (embed i))).list_sum_mem
  intro x hx
  obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hx
  exact Submodule.subset_span ⟨g, rfl⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512

end
