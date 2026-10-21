import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialDiagonalAction

/-! The Weyl-conjugate torus has the same long-root weight. Its short
weight is g² in rank two and g in higher rank. Both tori are actual
words and commute by their exact diagonal matrices. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem coxeterCycle_symm_inl_zero (r : ℕ) :
    (coxeterCycle r).symm (Sum.inl 0) = Sum.inr (Fin.last r) := by
  have h := congrArg (coxeterCycle r).symm (coxeterCycle_inr_last r)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem coxeterCycle_symm_inr_zero (r : ℕ) :
    (coxeterCycle r).symm (Sum.inr 0) = Sum.inl (Fin.last r) := by
  have h := congrArg (coxeterCycle r).symm (coxeterCycle_inl_last r)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem coxeterCycle_symm_inl_one (r : ℕ) (hr : 0 < r) :
    (coxeterCycle r).symm (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) = Sum.inl 0 := by
  have hp : coxeterCycle r (Sum.inl (0 : Fin (r + 1))) =
      Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inl_of_lt r 0 hr
  have h := congrArg (coxeterCycle r).symm hp
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem coxeterCycle_symm_inr_one (r : ℕ) (hr : 0 < r) :
    (coxeterCycle r).symm (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) = Sum.inr 0 := by
  have hp : coxeterCycle r (Sum.inr (0 : Fin (r + 1))) =
      Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inr_of_lt r 0 hr
  have h := congrArg (coxeterCycle r).symm hp
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem initialDiagonal_last_values (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    initialDiagonal K r hr g (Sum.inl (Fin.last r)) = (if r = 1 then (g : K) else 1) ∧
    initialDiagonal K r hr g (Sum.inr (Fin.last r)) = (if r = 1 then (g : K)⁻¹ else 1) := by
  have hn : (Fin.last r : Fin (r + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change r = 0 at hv
    omega
  have he : (Fin.last r : Fin (r + 1)) = (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) ↔ r = 1 := by
    constructor
    · exact fun h => congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  simp [initialDiagonal, coordinateTorusDiagonal, hn, he]

def shiftedInitialTorus (K : Type) [Field K] (r : ℕ) (g : Kˣ) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * initialTorus K r g * (coxeterWeyl K r)⁻¹

theorem shiftedInitialTorus_coe (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    ((shiftedInitialTorus K r g).val : Mat K (r + 1)) =
      Matrix.diagonal (initialDiagonal K r hr g ∘ (coxeterCycle r).symm) := by
  change ((coxeterWeyl K r).val : Mat K (r + 1)) *
    ((initialTorus K r g).val : Mat K (r + 1)) *
    (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) = _
  rw [initialTorus_coe K r hr]
  exact CFSGMonomialUnitRootAction.monomial_conjugation_diagonal
    (coxeterWeyl K r).val (coxeterCycle r).symm
    (coxeterSign K r ∘ (coxeterCycle r).symm) _ (coxeterWeyl_monomial K r)

theorem shiftedInitialTorus_short_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    shiftedInitialTorus K r g * initialShortRoot K r a * (shiftedInitialTorus K r g)⁻¹ =
      initialShortRoot K r ((if r = 1 then (g : K) ^ 2 else (g : K)) * a) := by
  have hv := initialDiagonal_values K r hr g
  have hl := initialDiagonal_last_values K r hr g
  apply initialShort_diagonal_conjugation K r hr (shiftedInitialTorus K r g)
    (initialDiagonal K r hr g ∘ (coxeterCycle r).symm) (shiftedInitialTorus_coe K r hr g)
  · simp only [Function.comp_apply, coxeterCycle_symm_inl_one r hr,
      coxeterCycle_symm_inl_zero, hv.1, hl.2]
    split_ifs <;> field_simp <;> ring
  · simp only [Function.comp_apply, coxeterCycle_symm_inr_one r hr,
      coxeterCycle_symm_inr_zero, hv.2.2.1, hl.1]
    split_ifs <;> field_simp <;> ring

theorem shiftedInitialTorus_long_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    shiftedInitialTorus K r g * secondLongRoot K r a * (shiftedInitialTorus K r g)⁻¹ =
      secondLongRoot K r ((g : K) ^ 2 * a) := by
  have hv := initialDiagonal_values K r hr g
  apply secondLong_diagonal_conjugation K r hr (shiftedInitialTorus K r g)
    (initialDiagonal K r hr g ∘ (coxeterCycle r).symm) (shiftedInitialTorus_coe K r hr g)
  simp only [Function.comp_apply, coxeterCycle_symm_inl_one r hr,
    coxeterCycle_symm_inr_one r hr, hv.1, hv.2.2.1]
  field_simp

theorem shiftedInitialTorus_commute (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    Commute (shiftedInitialTorus K r g) (initialTorus K r g) := by
  change shiftedInitialTorus K r g * initialTorus K r g =
    initialTorus K r g * shiftedInitialTorus K r g
  apply Subtype.ext
  apply Units.ext
  change ((shiftedInitialTorus K r g).val : Mat K (r + 1)) *
      ((initialTorus K r g).val : Mat K (r + 1)) =
    ((initialTorus K r g).val : Mat K (r + 1)) *
      ((shiftedInitialTorus K r g).val : Mat K (r + 1))
  rw [shiftedInitialTorus_coe K r hr, initialTorus_coe K r hr,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
