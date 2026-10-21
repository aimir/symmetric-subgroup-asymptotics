import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedRoot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationStarTorus
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction

/-! The actual star torus and its Weyl conjugate scale e2-e1 by g^-1
and g respectively. Both are diagonal in the SAME original coordinates,
so they commute. These are the second endpoint's one-root filter data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedTorusAction
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationInitialRootMatrices
open CFSGOrthogonalDGenerationShiftedRoot CFSGOrthogonalDGenerationStarTorus
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationCoxeterMonomial
variable (K : Type) [Field K]

theorem shifted_diagonal_conjugation (s : ℕ)
    (T : elementaryRootGroup K (s + 4)) (d : Index (s + 4) → K)
    (hT : (T.val : Mat K (s + 4)) = Matrix.diagonal d) (c a : K)
    (hp : d (Sum.inl (third s)) = c * d (Sum.inl (second s)))
    (hn : d (Sum.inr (second s)) = c * d (Sum.inr (third s))) :
    T * shiftedShortRoot K s a * T⁻¹ = shiftedShortRoot K s (c * a) := by
  let X : Mat K (s + 4) := Matrix.single (Sum.inl (third s)) (Sum.inl (second s)) 1 -
    Matrix.single (Sum.inr (second s)) (Sum.inr (third s)) 1
  have hr (b : K) : ((shiftedShortRoot K s b).val : Mat K (s + 4)) = 1 + b • X := by
    rw [shiftedShortRoot_coe]
    simp only [X, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
    abel
  apply Subtype.ext
  apply CFSGDiagonalUnitRootAction.root_line_conjugation T.val
    (shiftedShortRoot K s a).val (shiftedShortRoot K s (c * a)).val d X c a hT (hr a) (hr (c * a))
  intro i j hX
  by_cases hpos : (Sum.inl (third s) : Index (s + 4)) = i ∧ Sum.inl (second s) = j
  · rcases hpos with ⟨rfl, rfl⟩
    exact hp
  · by_cases hneg : (Sum.inr (second s) : Index (s + 4)) = i ∧ Sum.inr (third s) = j
    · rcases hneg with ⟨rfl, rfl⟩
      exact hn
    · have hz : X i j = 0 := by
        simp only [X, Matrix.sub_apply, Matrix.single_apply, hpos, hneg, if_false, sub_self]
      exact (hX hz).elim

theorem starDiagonal_first_values (s : ℕ) (g : Kˣ) :
    starDiagonal K s g (Sum.inl 0) = 1 ∧
    starDiagonal K s g (Sum.inr 0) = 1 ∧
    starDiagonal K s g (Sum.inl (second s)) = (g : K) ∧
    starDiagonal K s g (Sum.inr (second s)) = (g : K)⁻¹ ∧
    starDiagonal K s g (Sum.inl (third s)) = 1 ∧
    starDiagonal K s g (Sum.inr (third s)) = 1 := by
  simp [starDiagonal, Ne.symm (second_ne_zero s), Ne.symm (last_ne_zero s),
    third_ne_second, third_ne_last]

def conjugatedStarDiagonal (s : ℕ) (g : Kˣ) : Index (s + 4) → K :=
  starDiagonal K s g ∘ (cyclePerm (s + 2)).symm

theorem conjugatedStarTorus_coe (s : ℕ) (g : Kˣ) :
    (((coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) :
      Mat K (s + 4)) = Matrix.diagonal (conjugatedStarDiagonal K s g) := by
  change ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) *
    ((starTorus K s g).val : Mat K (s + 4)) *
      (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) = _
  rw [starTorus_coe]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K (s + 3)).val (cyclePerm (s + 2)).symm
    (coxeterColumnSign K (s + 2) ∘ (cyclePerm (s + 2)).symm)
    (starDiagonal K s g) (coxeter_monomial K (s + 2))

private theorem inverse_at {I : Type*} (σ : Equiv.Perm I) (x y : I) (h : σ y = x) :
    σ.symm x = y := by rw [← h, Equiv.symm_apply_apply]

theorem conjugatedStarDiagonal_values (s : ℕ) (g : Kˣ) :
    conjugatedStarDiagonal K s g (Sum.inl (third s)) = (g : K) ∧
    conjugatedStarDiagonal K s g (Sum.inl (second s)) = 1 ∧
    conjugatedStarDiagonal K s g (Sum.inr (second s)) = 1 ∧
    conjugatedStarDiagonal K s g (Sum.inr (third s)) = (g : K)⁻¹ := by
  have h3p : (cyclePerm (s + 2)).symm (Sum.inl (third s)) = Sum.inl (second s) :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) false 1 (by omega))
  have h1p : (cyclePerm (s + 2)).symm (Sum.inl (second s)) = Sum.inl 0 :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) false 0 (by omega))
  have h1n : (cyclePerm (s + 2)).symm (Sum.inr (second s)) = Sum.inr 0 :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) true 0 (by omega))
  have h3n : (cyclePerm (s + 2)).symm (Sum.inr (third s)) = Sum.inr (second s) :=
    inverse_at (cyclePerm (s + 2)) _ _ (cyclePerm_shift (s + 2) true 1 (by omega))
  have hv := starDiagonal_first_values K s g
  simpa only [conjugatedStarDiagonal, Function.comp_apply, h3p, h1p, h1n, h3n]
    using And.intro hv.2.2.1 (And.intro hv.1 (And.intro hv.2.1 hv.2.2.2.1))

theorem starTorus_shifted_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    starTorus K s g * shiftedShortRoot K s a * (starTorus K s g)⁻¹ =
      shiftedShortRoot K s ((g : K)⁻¹ * a) := by
  have hv := starDiagonal_first_values K s g
  apply shifted_diagonal_conjugation K s (starTorus K s g) (starDiagonal K s g)
    (starTorus_coe K s g)
  · rw [hv.2.2.2.2.1, hv.2.2.1, inv_mul_cancel₀ (Units.ne_zero g)]
  · rw [hv.2.2.2.1, hv.2.2.2.2.2, mul_one]

theorem conjugatedStarTorus_shifted_conjugation (s : ℕ) (g : Kˣ) (a : K) :
    (coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹) *
      shiftedShortRoot K s a *
        (coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹)⁻¹ =
      shiftedShortRoot K s ((g : K) * a) := by
  have hv := conjugatedStarDiagonal_values K s g
  apply shifted_diagonal_conjugation K s _ (conjugatedStarDiagonal K s g)
    (conjugatedStarTorus_coe K s g)
  · rw [hv.1, hv.2.1, mul_one]
  · rw [hv.2.2.1, hv.2.2.2, mul_inv_cancel₀ (Units.ne_zero g)]

theorem conjugatedStarTorus_commutes (s : ℕ) (g : Kˣ) :
    Commute (coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹)
      (starTorus K s g) := by
  change _ * starTorus K s g = starTorus K s g * _
  apply Subtype.ext
  apply Units.ext
  change (((coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) :
      Mat K (s + 4)) * ((starTorus K s g).val : Mat K (s + 4)) =
    ((starTorus K s g).val : Mat K (s + 4)) *
      (((coxeterWeyl K (s + 3) * starTorus K s g * (coxeterWeyl K (s + 3))⁻¹).val) : Mat K (s + 4))
  rw [conjugatedStarTorus_coe, starTorus_coe, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedTorusAction
