import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterShortAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialCommutation
import Mathlib.Tactic.Group

/-! The purified terminal short-root orbit under alpha(1)W. It runs
from the positive last coordinate through the negative coordinates only
up to the penultimate one, where alpha still commutes with the output.
No rank-parity branch or already-recovered pure W is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCleanedOrbit
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationInitialCommutation CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationCoxeter CFSGOrthogonalBGenerationCoxeterShortAction
variable (K : Type) [Field K]

private theorem cleaned_conjugation (s : ℕ) (b : Fin (s + 3) ⊕ Fin (s + 3))
    (hp : CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b ≠ Sum.inl (penIndex s))
    (hn : CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b ≠ Sum.inr (lastIndex s)) (a : K) :
    (alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val) * shortUnit K (s + 3) b a *
        (alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val)⁻¹ =
      shortUnit K (s + 3) (CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b)
        ((-coxeterSign K (s + 2) (Sum.inl b)) * a) := by
  let V := shortUnit K (s + 3) (CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b)
    ((-coxeterSign K (s + 2) (Sum.inl b)) * a)
  have hc : Commute (alphaUnit K s 1) V := alpha_short_commute K s _ hp hn 1 _
  calc
    _ = alphaUnit K s 1 *
        ((coxeterWeyl K (s + 2)).val * shortUnit K (s + 3) b a * (coxeterWeyl K (s + 2)).val⁻¹) *
        (alphaUnit K s 1)⁻¹ := by group
    _ = alphaUnit K s 1 * V * (alphaUnit K s 1)⁻¹ := by rw [coxeter_short_conjugation]
    _ = V := by rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem full_short_line_of_cleaned (s : ℕ) (H : Subgroup (Mat K (s + 3))ˣ)
    (hY : alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val ∈ H)
    (b : Fin (s + 3) ⊕ Fin (s + 3))
    (hp : CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b ≠ Sum.inl (penIndex s))
    (hn : CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b ≠ Sum.inr (lastIndex s))
    (hB : ∀ a, shortUnit K (s + 3) b a ∈ H) :
    ∀ a, shortUnit K (s + 3) (CFSGSymplecticSerreMatrices.coxeterCycle (s + 2) b) a ∈ H := by
  intro a
  let l := -coxeterSign K (s + 2) (Sum.inl b)
  have hll : l * l = 1 := by
    simpa only [l, neg_mul_neg] using coxeterSign_mul_self K (s + 2) (Sum.inl b)
  have hh := H.mul_mem (H.mul_mem hY (hB (l * a))) (H.inv_mem hY)
  rw [cleaned_conjugation K s b hp hn] at hh
  have he : (-coxeterSign K (s + 2) (Sum.inl b)) * (l * a) = a := by
    change l * (l * a) = a
    rw [← mul_assoc, hll, one_mul]
  simpa only [he] using hh

theorem negative_lines_of_cleaned (s : ℕ) (H : Subgroup (Mat K (s + 3))ˣ)
    (hY : alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val ∈ H)
    (hB : ∀ a, betaUnit K s a ∈ H) :
    ∀ (i : Fin (s + 3)), i.val ≤ s + 1 → ∀ a, shortUnit K (s + 3) (Sum.inr i) a ∈ H := by
  have hzero : ∀ a, shortUnit K (s + 3) (Sum.inr (0 : Fin (s + 3))) a ∈ H := by
    have hh := full_short_line_of_cleaned K s H hY (Sum.inl (lastIndex s))
      (by rw [show lastIndex s = Fin.last (s + 2) from rfl,
          CFSGSymplecticSerreMatrices.coxeterCycle_inl_last]; intro h; cases h)
      (by
        rw [show lastIndex s = Fin.last (s + 2) from rfl,
          CFSGSymplecticSerreMatrices.coxeterCycle_inl_last]
        intro he
        have hv := congrArg Fin.val (Sum.inr.inj he)
        change 0 = s + 2 at hv
        omega) hB
    simpa only [lastIndex, CFSGSymplecticSerreMatrices.coxeterCycle_inl_last] using hh
  have hneg : ∀ j : ℕ, ∀ hj : j ≤ s + 1, ∀ a,
      shortUnit K (s + 3) (Sum.inr (⟨j, by omega⟩ : Fin (s + 3))) a ∈ H := by
    intro j
    induction j with
    | zero => intro _ a; exact hzero a
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hcy := CFSGSymplecticSerreMatrices.coxeterCycle_inr_of_lt (s + 2) j (by omega : j < s + 2)
      have hh := full_short_line_of_cleaned K s H hY (Sum.inr (⟨j, by omega⟩ : Fin (s + 3)))
        (by rw [hcy]; intro h; cases h)
        (by
          rw [hcy]
          intro he
          have hv := congrArg Fin.val (Sum.inr.inj he)
          change j + 1 = s + 2 at hv
          omega) hprev
      simpa only [hcy] using hh
  intro i hi
  exact hneg i.val hi

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCleanedOrbit
