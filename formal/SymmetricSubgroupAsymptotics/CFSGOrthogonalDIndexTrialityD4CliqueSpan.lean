import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The planes through a fixed line span the containing space. In
particular global top and star cliques recover their ambient spaces;
this distinguishes dimension-three tops from dimension-four stars. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueSpan
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem line_star_covers_space (U M : Submodule K V) (hU : Module.finrank K U = 1)
    (hUM : U ≤ M) (hM : 2 ≤ Module.finrank K M) (x : V) (hx : x ∈ M) :
    ∃ P : Submodule K V, Module.finrank K P = 2 ∧ U ≤ P ∧ P ≤ M ∧ x ∈ P := by
  by_cases hxU : x ∈ U
  · have hn : ¬ M ≤ U := by
      intro h
      have hd := Submodule.finrank_mono h
      rw [hU] at hd
      omega
    obtain ⟨w, hwM, hwU⟩ := Set.not_subset.mp hn
    refine ⟨U ⊔ Submodule.span K {w}, ?_, le_sup_left, ?_, Submodule.mem_sup_left hxU⟩
    · rw [Submodule.finrank_sup_span_singleton hwU, hU]
    · exact sup_le hUM ((Submodule.span_singleton_le_iff_mem w M).mpr hwM)
  · refine ⟨U ⊔ Submodule.span K {x}, ?_, le_sup_left, ?_,
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩
    · rw [Submodule.finrank_sup_span_singleton hxU, hU]
    · exact sup_le hUM ((Submodule.span_singleton_le_iff_mem x M).mpr hx)

theorem star_planes_span_space (U M : Submodule K V) (hU : Module.finrank K U = 1)
    (hUM : U ≤ M) (hM : 2 ≤ Module.finrank K M) :
    sSup {P : Submodule K V | Module.finrank K P = 2 ∧ U ≤ P ∧ P ≤ M} = M := by
  apply le_antisymm
  · exact sSup_le (fun P hP => hP.2.2)
  · intro x hx
    obtain ⟨P, hP, hUP, hPM, hxP⟩ := line_star_covers_space U M hU hUM hM x hx
    exact (le_sSup (show P ∈ {P : Submodule K V |
      Module.finrank K P = 2 ∧ U ≤ P ∧ P ≤ M} from ⟨hP, hUP, hPM⟩)) hxP

theorem two_planes_span_space (M : Submodule K V) (hM : 2 ≤ Module.finrank K M) :
    sSup {P : Submodule K V | Module.finrank K P = 2 ∧ P ≤ M} = M := by
  apply le_antisymm
  · exact sSup_le (fun P hP => hP.2)
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    · let U : Submodule K V := Submodule.span K {x}
      have hU : Module.finrank K U = 1 := finrank_span_singleton hx0
      have hUM : U ≤ M := (Submodule.span_singleton_le_iff_mem x M).mpr hx
      obtain ⟨P, hP, _, hPM, hxP⟩ := line_star_covers_space U M hU hUM hM x hx
      exact (le_sSup (show P ∈ {P : Submodule K V |
        Module.finrank K P = 2 ∧ P ≤ M} from ⟨hP, hPM⟩)) hxP

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueSpan
