import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! A connected bipartite incidence geometry has exactly the global
orientation ambiguity. Agreement at one vertex determines a proper
two-colouring everywhere; the only other possibility reverses every
colour. No finite geometry or group-classification premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGConnectedBipartiteOrientation
variable {V : Type*} {Γ : SimpleGraph V}

theorem coloring_eq_of_eq_at (hΓ : Γ.Connected) (v₀ : V)
    (c d : Γ.Coloring Bool) (h₀ : c v₀ = d v₀) : c = d := by
  ext v
  obtain ⟨p⟩ := hΓ v₀ v
  have hr : ((c v₀ : Bool) ↔ c v) ↔ ((d v₀ : Bool) ↔ d v) :=
    (c.even_length_iff_congr p).symm.trans (d.even_length_iff_congr p)
  rw [h₀] at hr
  apply Bool.eq_iff_iff.mpr
  tauto

theorem eq_or_global_complement (hΓ : Γ.Connected) (c d : Γ.Coloring Bool) :
    c = d ∨ ∀ v, d v = !(c v) := by
  obtain ⟨v₀⟩ := hΓ.nonempty
  by_cases h₀ : c v₀ = d v₀
  · exact Or.inl (coloring_eq_of_eq_at hΓ v₀ c d h₀)
  · right
    intro v
    have hne : c v ≠ d v := by
      intro hv
      exact h₀ (congrArg (fun z : Γ.Coloring Bool => z v₀)
        (coloring_eq_of_eq_at hΓ v c d hv))
    cases hc : c v <;> cases hd : d v <;> simp_all

theorem evaluation_injective (hΓ : Γ.Connected) (v₀ : V) :
    Function.Injective (fun c : Γ.Coloring Bool => c v₀) := by
  intro c d h
  exact coloring_eq_of_eq_at hΓ v₀ c d h

theorem card_colorings_le_two (hΓ : Γ.Connected) : Nat.card (Γ.Coloring Bool) ≤ 2 := by
  obtain ⟨v₀⟩ := hΓ.nonempty
  simpa using Nat.card_le_card_of_injective (fun c : Γ.Coloring Bool => c v₀)
    (evaluation_injective hΓ v₀)

end SymmetricSubgroupAsymptotics.CFSGConnectedBipartiteOrientation
