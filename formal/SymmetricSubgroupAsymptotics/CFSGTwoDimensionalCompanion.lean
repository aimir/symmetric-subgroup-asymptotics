import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! An actual nonzero vector in a two-dimensional original submodule
extends to an actual independent pair spanning the SAME submodule. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
variable {K I : Type*} [Field K] [Fintype I]

theorem exists_companion (P : Submodule K (I → K)) (hdim : Module.finrank K P = 2)
    (u : I → K) (huP : u ∈ P) (hu : u ≠ 0) :
    ∃ v ∈ P, (∀ c : K, v ≠ c • u) ∧ Submodule.span K {u, v} = P := by
  classical
  have hex : ∃ v ∈ P, ∀ c : K, v ≠ c • u := by
    by_contra! h
    have hle : P ≤ Submodule.span K {u} := by
      intro v hv
      obtain ⟨c, hc⟩ := h v hv
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    have hb := Submodule.finrank_mono hle
    rw [hdim, finrank_span_singleton hu] at hb
    omega
  obtain ⟨v, hvP, hnot⟩ := hex
  refine ⟨v, hvP, hnot, ?_⟩
  have hi : LinearIndependent K ![u, v] :=
    (LinearIndependent.pair_iff' hu).mpr (fun c he => hnot c he.symm)
  have hr : Set.range ![u, v] = ({u, v} : Set (I → K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (hx | hx)
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
  have hd := finrank_span_eq_card hi
  rw [hr, Fintype.card_fin] at hd
  have hle : Submodule.span K {u, v} ≤ P := by
    apply Submodule.span_le.mpr
    rintro x (hx | hx)
    · rcases hx with rfl
      exact huP
    · rcases hx with rfl
      exact hvP
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hdim, hd])

end SymmetricSubgroupAsymptotics.CFSGTwoDimensionalSubmoduleBasis
