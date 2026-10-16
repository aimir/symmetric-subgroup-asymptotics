import SymmetricSubgroupAsymptotics.BinaryFourAmbientNakayama

/-! The literal diagonal plane is the monolith of the induced module.
The witness is one of four actual Klein differences, before any quotient. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def diagonal (a : Local) : Module := fun _ => a

def bottomCandidate (w : Module) : Fin 4 → Module :=
  ![w, ambientDifferenceU w, ambientDifferenceV w,
    ambientDifferenceU (ambientDifferenceV w)]

theorem nonzero_bottom_candidate (w : Module) (hw : w ≠ 0) :
    ∃ i : Fin 4, ∃ a : Local, a ≠ 0 ∧ bottomCandidate w i = diagonal a := by
  have exactIdentity : ∀ w : Module, w ≠ 0 →
      ∃ i : Fin 4, ∃ a : Local, a ≠ 0 ∧ bottomCandidate w i = diagonal a := by
    decide +kernel
  exact exactIdentity w hw

theorem diagonal_cycle (a : Local) :
    ambientCycle (diagonal a) = diagonal (localCycle a) := by rfl

theorem diagonal_mem_of_ne_bot
    (E : Submodule Scalar Module) (hne : E ≠ ⊥)
    (hU : ∀ w ∈ E, ambientDifferenceU w ∈ E)
    (hV : ∀ w ∈ E, ambientDifferenceV w ∈ E)
    (hC : ∀ w ∈ E, ambientCycle w ∈ E)
    (a : Local) : diagonal a ∈ E := by
  obtain ⟨w, hw, hnonzero⟩ := E.ne_bot_iff.mp hne
  obtain ⟨i, b, hb, hcand⟩ := nonzero_bottom_candidate w hnonzero
  have hcandidate : bottomCandidate w i ∈ E := by
    fin_cases i
    · exact hw
    · exact hU w hw
    · exact hV w hw
    · exact hU _ (hV w hw)
  rw [hcand] at hcandidate
  obtain ⟨s, t, hst⟩ := localCycle_generates b hb a
  have hmem := E.add_mem (E.smul_mem s hcandidate)
    (E.smul_mem t (hC _ hcandidate))
  rw [diagonal_cycle] at hmem
  have heq : s • diagonal b + t • diagonal (localCycle b) = diagonal a := by
    funext j
    exact hst
  rw [heq] at hmem
  exact hmem

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
