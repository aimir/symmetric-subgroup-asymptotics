import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterShortAction

/-! Once the actual pure B Coxeter word is recovered, its literal
signed coordinate cycle carries the full terminal short-root line to
every positive and negative coordinate, in every rank and characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationPureShortOrbit
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationCoxeter CFSGOrthogonalBGenerationCoxeterShortAction
variable (K : Type) [Field K]

private def point {r : ℕ} (side : Bool) (i : Fin r) : Fin r ⊕ Fin r :=
  if side then Sum.inr i else Sum.inl i

private theorem side_coverage (r : ℕ) (H : Subgroup (Mat K (r + 1))ˣ)
    (hW : (coxeterWeyl K r).val ∈ H) (side : Bool)
    (h0 : ∀ a, shortUnit K (r + 1) (point side (0 : Fin (r + 1))) a ∈ H) :
    ∀ (i : Fin (r + 1)) (a : K), shortUnit K (r + 1) (point side i) a ∈ H := by
  have aux : ∀ j : ℕ, ∀ hj : j ≤ r, ∀ a,
      shortUnit K (r + 1) (point side (⟨j, by omega⟩ : Fin (r + 1))) a ∈ H := by
    intro j
    induction j with
    | zero => intro _ a; exact h0 a
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hcy : CFSGSymplecticSerreMatrices.coxeterCycle r
          (point side (⟨j, by omega⟩ : Fin (r + 1))) =
          point side (⟨j + 1, by omega⟩ : Fin (r + 1)) := by
        cases side
        · exact CFSGSymplecticSerreMatrices.coxeterCycle_inl_of_lt r j (by omega)
        · exact CFSGSymplecticSerreMatrices.coxeterCycle_inr_of_lt r j (by omega)
      have hh := full_short_line_transfer K r H hW
        (point side (⟨j, by omega⟩ : Fin (r + 1))) hprev
      simpa only [hcy] using hh
  intro i
  exact aux i.val (by omega)

theorem all_short_lines_of_weyl (r : ℕ) (H : Subgroup (Mat K (r + 1))ˣ)
    (hW : (coxeterWeyl K r).val ∈ H)
    (hLast : ∀ a, shortUnit K (r + 1) (Sum.inl (Fin.last r)) a ∈ H) :
    ∀ (b : Fin (r + 1) ⊕ Fin (r + 1)) (a : K), shortUnit K (r + 1) b a ∈ H := by
  have hneg0 : ∀ a, shortUnit K (r + 1) (Sum.inr (0 : Fin (r + 1))) a ∈ H := by
    have hh := full_short_line_transfer K r H hW (Sum.inl (Fin.last r)) hLast
    simpa only [CFSGSymplecticSerreMatrices.coxeterCycle_inl_last] using hh
  have hneg := side_coverage K r H hW true hneg0
  have hpos0 : ∀ a, shortUnit K (r + 1) (Sum.inl (0 : Fin (r + 1))) a ∈ H := by
    have hh := full_short_line_transfer K r H hW (Sum.inr (Fin.last r)) (hneg (Fin.last r))
    simpa only [CFSGSymplecticSerreMatrices.coxeterCycle_inr_last] using hh
  have hpos := side_coverage K r H hW false hpos0
  rintro (i | i) a
  · exact hpos i a
  · exact hneg i a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationPureShortOrbit
