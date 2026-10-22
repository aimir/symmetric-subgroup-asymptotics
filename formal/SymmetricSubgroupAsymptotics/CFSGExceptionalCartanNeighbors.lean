import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanConnected

/-! Actual adjacent neighbors in the three pinned exceptional diagrams.
These discharge the local mixed-A2 rigidity premise at every simple root. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalCartanNeighbors

theorem E6_neighbor (j : Fin 6) : ∃ k, CartanMatrix.E₆ j k = -1 := by
  fin_cases j
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩

theorem E7_neighbor (j : Fin 7) : ∃ k, CartanMatrix.E₇ j k = -1 := by
  fin_cases j
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩

theorem E8_neighbor (j : Fin 8) : ∃ k, CartanMatrix.E₈ j k = -1 := by
  fin_cases j
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨6, by decide⟩

end SymmetricSubgroupAsymptotics.CFSGExceptionalCartanNeighbors
