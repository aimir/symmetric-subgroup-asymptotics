import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootLineTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedRootCommutation

/-! The actual cleaned D generator propagates the initial star line to
negative coordinate zero. Only the last-coordinate sign is existential;
it is never inferred from a group order or replaced by a parity premise.
The two endpoint signs are retained for the subsequent recovery argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedOrbit
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationInitialElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationRootLineTransport
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationSignedRootLineTransport
open CFSGOrthogonalDGenerationCleanedRootCommutation
variable (K : Type) [Field K]

def lastColumn (s : ℕ) (side : Bool) : Index (s + 4) :=
  if side then Sum.inr (last (s + 2)) else Sum.inl (last (s + 2))

theorem cycle_lastColumn (s : ℕ) (side : Bool) :
    cyclePerm (s + 2) (lastColumn s side) = lastColumn s (!side) := by
  cases side <;> simp only [lastColumn, Bool.false_eq_true, if_false, if_true,
    Bool.not_false, Bool.not_true, last, cyclePerm_positive_last, cyclePerm_negative_last]

theorem endpoint_line (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hY : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2))))) :
    ∃ side : Bool, HasRootLine H
      (rootArray K (Sum.inr (0 : Fin (s + 4))) (lastColumn s side)) := by
  have hlines : ∀ j : ℕ, ∀ hj : j < s + 2, ∃ side : Bool,
      HasRootLine H (rootArray K (Sum.inl (⟨j + 1, by omega⟩ : Fin (s + 4)))
        (lastColumn s side)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨true, hB⟩
    | succ j ih =>
      intro hj
      obtain ⟨side, hline⟩ := ih (by omega)
      have hm : cyclePerm (s + 2) (Sum.inl (⟨j + 1, by omega⟩ : Fin (s + 4))) =
          Sum.inl (⟨j + 2, by omega⟩ : Fin (s + 4)) :=
        cyclePerm_shift (s + 2) false (j + 1) (by omega)
      have hc : ∀ t, Commute ((initialShortRoot K s 1).val : Mat K (s + 4))
          (rootArray K (cyclePerm (s + 2) (Sum.inl (⟨j + 1, by omega⟩ : Fin (s + 4))))
            (cyclePerm (s + 2) (lastColumn s side)) t) := by
        intro t
        rw [hm, cycle_lastColumn]
        exact initial_commutes_moving K s ⟨j + 2, by omega⟩
          (by intro he; have hv := congrArg Fin.val he; change j + 2 = 0 at hv; omega)
          (by intro he; have hv := congrArg Fin.val he; change j + 2 = 1 at hv; omega)
          (!side) 1 t
      have hn := cleaned_coxeter_line_transfer K (s + 2) H
        (initialShortRoot K s 1).val hY _ _ hc hline
      refine ⟨!side, ?_⟩
      simpa only [hm, cycle_lastColumn, Nat.succ_eq_add_one, Nat.add_assoc] using hn
  obtain ⟨side, hline⟩ := hlines (s + 1) (by omega)
  have hm : cyclePerm (s + 2) (Sum.inl (⟨s + 1 + 1, by omega⟩ : Fin (s + 4))) =
      Sum.inr 0 := cyclePerm_positive_penultimate (s + 2)
  have hc : ∀ t, Commute ((initialShortRoot K s 1).val : Mat K (s + 4))
      (rootArray K (cyclePerm (s + 2) (Sum.inl (⟨s + 1 + 1, by omega⟩ : Fin (s + 4))))
        (cyclePerm (s + 2) (lastColumn s side)) t) := by
    intro t
    rw [hm, cycle_lastColumn]
    exact initial_commutes_endpoint K s (!side) 1 t
  have hn := cleaned_coxeter_line_transfer K (s + 2) H
    (initialShortRoot K s 1).val hY _ _ hc hline
  exact ⟨!side, by simpa only [hm, cycle_lastColumn] using hn⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedOrbit
