import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterMonomial
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialDiagonalAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter

/-! Actual first-root extraction for the nonbinary D pair. Every torus,
Weyl word and root line is the literal element of the original elementary
group. The proof establishes a full star line and the cleaned mixed word;
the later orbit and parity arguments are separate generation obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialExtraction
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationInitialDiagonalAction
open CFSGOrthogonalDGenerationCoxeterMonomial CFSGOrthogonalDBinaryCyclePermutation
variable (K : Type) [Field K]

theorem torusPermutation_pen (s : ℕ) : torusPermutation s (pen (s + 2)) = 0 := by
  simp [torusPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Ne.symm (second_ne_pen s), pen_ne_last]

theorem initialTorusDiagonal_pen (s : ℕ) (g : Kˣ) :
    initialTorusDiagonal K s g (Sum.inl (pen (s + 2))) = 1 ∧
    initialTorusDiagonal K s g (Sum.inr (pen (s + 2))) = 1 := by
  simp [initialTorusDiagonal, torusPermutation_pen, forkDiagonal,
    Ne.symm (pen_ne_zero s), Ne.symm (last_ne_zero s)]

def conjugatedDiagonal (s : ℕ) (g : Kˣ) : Index (s + 4) → K :=
  initialTorusDiagonal K s g ∘ (cyclePerm (s + 2)).symm

theorem conjugatedTorus_coe (s : ℕ) (g : Kˣ) :
    (((coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) :
      Mat K (s + 4)) = Matrix.diagonal (conjugatedDiagonal K s g) := by
  change ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) *
    ((initialTorus K s g).val : Mat K (s + 4)) *
      (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) = _
  rw [initialTorus_coe]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K (s + 3)).val (cyclePerm (s + 2)).symm
    (coxeterColumnSign K (s + 2) ∘ (cyclePerm (s + 2)).symm)
    (initialTorusDiagonal K s g) (coxeter_monomial K (s + 2))

private theorem inverse_at {I : Type*} (σ : Equiv.Perm I) (x y : I) (h : σ y = x) :
    σ.symm x = y := by rw [← h, Equiv.symm_apply_apply]

theorem conjugatedDiagonal_values (s : ℕ) (g : Kˣ) :
    conjugatedDiagonal K s g (Sum.inl 0) = 1 ∧
    conjugatedDiagonal K s g (Sum.inl (second s)) = (g : K) ∧
    conjugatedDiagonal K s g (Sum.inr 0) = 1 ∧
    conjugatedDiagonal K s g (Sum.inr (second s)) = (g : K)⁻¹ ∧
    conjugatedDiagonal K s g (Sum.inl (last (s + 2))) = 1 ∧
    conjugatedDiagonal K s g (Sum.inr (last (s + 2))) = 1 := by
  have h0p := inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_negative_penultimate (s + 2))
  have h0n := inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_positive_penultimate (s + 2))
  have h1p : (cyclePerm (s + 2)).symm (Sum.inl (second s)) = Sum.inl 0 :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) false 0 (by omega))
  have h1n : (cyclePerm (s + 2)).symm (Sum.inr (second s)) = Sum.inr 0 :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) true 0 (by omega))
  have hLp := inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_negative_last (s + 2))
  have hLn := inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_positive_last (s + 2))
  have hv := initialTorusDiagonal_values K s g
  have hp := initialTorusDiagonal_pen K s g
  simpa only [conjugatedDiagonal, Function.comp_apply, pen, last,
    h0p, h0n, h1p, h1n, hLp, hLn]
    using And.intro hp.2 (And.intro hv.1 (And.intro hp.1
      (And.intro hv.2.2.1 (And.intro hv.2.2.2.2.2 hv.2.2.2.2.1))))

theorem conjugatedTorus_short_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    (coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹) *
      initialShortRoot K s a *
        (coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹)⁻¹ =
      initialShortRoot K s ((g : K) * a) := by
  have hv := conjugatedDiagonal_values K s g
  apply initialShort_diagonal_conjugation K s _ (conjugatedDiagonal K s g)
    (conjugatedTorus_coe K s g)
  · rw [hv.2.1, hv.1, mul_one]
  · rw [hv.2.2.1, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

theorem conjugatedTorus_star_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    (coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹) *
      initialStarRoot K s false a *
        (coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹)⁻¹ =
      initialStarRoot K s false ((g : K) * a) := by
  have hv := conjugatedDiagonal_values K s g
  apply initialStar_diagonal_conjugation K s _ (conjugatedDiagonal K s g)
    (conjugatedTorus_coe K s g)
  · rw [hv.2.1, hv.2.2.2.2.2, mul_one]
  · rw [hv.2.2.2.2.1, hv.2.2.2.1, mul_inv_cancel₀ (Units.ne_zero g)]

theorem conjugatedTorus_commutes (s : ℕ) (g : Kˣ) :
    Commute (coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹)
      (initialTorus K s g) := by
  change _ * initialTorus K s g = initialTorus K s g * _
  apply Subtype.ext
  apply Units.ext
  change (((coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) :
      Mat K (s + 4)) * ((initialTorus K s g).val : Mat K (s + 4)) =
    ((initialTorus K s g).val : Mat K (s + 4)) *
      (((coxeterWeyl K (s + 3) * initialTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) :
        Mat K (s + 4))
  rw [conjugatedTorus_coe, initialTorus_coe, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

theorem star_line_and_cleaned_word [Finite K] (s : ℕ) (hcard : 3 ≤ Nat.card K)
    (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (elementaryRootGroup K (s + 4)))
    (hT : initialTorus K s g ∈ H) (hy : initialMixedWeyl K s ∈ H) :
    (∀ a, initialStarRoot K s false a ∈ H) ∧
      initialShortRoot K s 1 * coxeterWeyl K (s + 3) ∈ H := by
  have hB := CFSGOrthogonalDGenerationScalarFilter.second_line_of_pair hcard g hg
    (initialShortRoot K s) (initialStarRoot K s false)
    (initialShortRoot_add K s) (initialShortRoot_zero K s)
    (initialStarRoot_add K s false) (initialStarRoot_zero K s false)
    (CFSGOrthogonalDGenerationRootArrays.initial_lines_commute s)
    (initialTorus K s g) (coxeterWeyl K (s + 3)) (g : K)
    (initialTorus_short_conjugation K s g) (initialTorus_star_conjugation K s g)
    (conjugatedTorus_short_conjugation K s g) (conjugatedTorus_star_conjugation K s g)
    (conjugatedTorus_commutes K s g) H hT hy
  refine ⟨hB, ?_⟩
  exact CFSGOrthogonalDGenerationScalarFilter.cleaned_word_mem _ _
    (CFSGOrthogonalDGenerationRootArrays.initial_lines_commute s 1 1) _ H (hB 1) hy

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialExtraction
