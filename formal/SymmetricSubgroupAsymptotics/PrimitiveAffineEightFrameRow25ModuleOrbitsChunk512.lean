import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsData

/-! Selected row 25 vector orbits 512–531. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512

abbrev Source := PrimitiveAffineEightFrameRow25ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop16TopCertificate.group

def embed (i : Fin 20) : Fin 532 :=
  ⟨512 + i.val, by omega⟩

theorem minimal : ∀ i : Fin 20, ∀ g,
    binaryVectorMask (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i)) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow25ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))) :=
  (Fin.addCases (m := 10) (n := 10) (by native_decide) (by native_decide))

theorem stabilizer_card : ∀ i : Fin 20,
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
      (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))) =
        PrimitiveAffineEightFrameRow25ModuleOrbitsData.stabilizerCard (embed i) := by
  intro i
  letI : DecidablePred (fun g : Source ↦
      g ∈ representationVectorStabilizer
        PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))) :=
    fun g ↦ decidable_of_iff
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i)) = PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))
      Iff.rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> native_decide

private def relationWords (i : Fin 20) : List Source :=
  (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3,3]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4,3]]) else (if i.val < 3 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]] else (if i.val < 4 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3,3]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,3]]))) else (if i.val < 7 then (if i.val < 6 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4]]) else (if i.val < 8 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4,3]] else (if i.val < 9 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3,3]])))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]]) else (if i.val < 13 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]] else (if i.val < 14 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3]]))) else (if i.val < 17 then (if i.val < 16 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3]]) else (if i.val < 18 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4]] else (if i.val < 19 then [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,4,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4,3,4]] else [PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord [3,4,3]])))))

theorem orbit_mem_chart : ∀ i : Fin 20,
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic (embed i)))).2.inclusion
        ((PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic (embed i)))).2.coordinates
          (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))) =
      PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i) :=
  (Fin.addCases (m := 10) (n := 10) (by native_decide) (by native_decide))

theorem relation_eq : ∀ i : Fin 20,
    PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic (embed i)) =
      ((relationWords i).map (fun g ↦
        PrimitiveAffineEightFrameRow25ModuleRepresentation.representation g
          (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i)))).sum :=
  (Fin.addCases (m := 10) (n := 10) (by native_decide) (by native_decide))

theorem canonical_mem_orbit_span (i : Fin 20) :
    PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic (embed i)) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i)) := by
  rw [relation_eq i]
  apply (binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative (embed i))).list_sum_mem
  intro x hx
  obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hx
  exact Submodule.subset_span ⟨g, rfl⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512

end
