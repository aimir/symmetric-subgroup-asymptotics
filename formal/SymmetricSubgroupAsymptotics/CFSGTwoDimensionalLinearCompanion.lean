import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
import SymmetricSubgroupAsymptotics.CFSGSingularPairSpan

/-! A specified nonzero vector of a two-dimensional submodule extends
to an independent spanning pair in any ambient module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem exists_companion (P : Submodule K V) (hdim : Module.finrank K P = 2)
    (u : V) (huP : u ∈ P) (hu : u ≠ 0) :
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
  have hd := CFSGSingularPairSpan.finrank_pair u v hu hnot
  have hle : Submodule.span K {u, v} ≤ P := by
    apply Submodule.span_le.mpr
    rintro x (hx | hx)
    · rcases hx with rfl
      exact huP
    · rcases hx with rfl
      exact hvP
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hdim, hd])

end SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
