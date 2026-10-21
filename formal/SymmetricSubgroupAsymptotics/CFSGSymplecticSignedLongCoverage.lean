import SymmetricSubgroupAsymptotics.CFSGSymplecticSignedShortCoverage

/-! Full long-root parameter coverage through the actual signed
Coxeter cycle, in every characteristic. The terminal crossing has
coefficient -1, which is retained and inverted in parameter space. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines

def coordinateLongRootMatrix (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) : Mat K (r + 1) :=
  Matrix.single (coordinatePoint r side i) (coordinatePoint r (!side) i) 1

theorem coxeter_longRoot_shift (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin (r + 1)) (hi : i.val < r) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) * coordinateLongRootMatrix K r side i *
      (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      coordinateLongRootMatrix K r side (⟨i.val + 1, Nat.succ_lt_succ hi⟩ : Fin (r + 1)) := by
  simp only [coordinateLongRootMatrix, coxeter_single_conjugation,
    coxeterSign_point_of_lt K r side i hi, coxeterSign_point_of_lt K r (!side) i hi,
    coxeterCycle_point_of_lt r side i hi, coxeterCycle_point_of_lt r (!side) i hi,
    div_one, one_smul]

theorem coxeter_upper_longRoot_crossing (K : Type) [Field K] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *
      coordinateLongRootMatrix K r false (Fin.last r) *
      (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      (-1 : K) • coordinateLongRootMatrix K r true (0 : Fin (r + 1)) := by
  simp only [coordinateLongRootMatrix, coordinatePoint, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, coxeter_single_conjugation,
    coxeterCycle_inl_last, coxeterCycle_inr_last, coxeterSign]
  have he : (-1 : K) ^ r / (-1 : K) ^ (r + 1) = -1 := by
    rw [pow_succ]
    field_simp <;> ring
  rw [he]

theorem coordinate_long_side_coverage (K : Type) [Field K] (r : ℕ)
    (H : Subgroup ((Mat K (r + 1))ˣ)) (hW : (coxeterWeyl K r).val ∈ H)
    (side : Bool) (h0 : HasRootLine H (coordinateLongRootMatrix K r side 0)) :
    ∀ i : Fin (r + 1), HasRootLine H (coordinateLongRootMatrix K r side i) := by
  have aux : ∀ k : ℕ, ∀ hk : k ≤ r,
      HasRootLine H (coordinateLongRootMatrix K r side (⟨k, by omega⟩ : Fin (r + 1))) := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      have hstep := coxeter_longRoot_shift K r side
        (⟨k, by omega⟩ : Fin (r + 1)) (by change k < r; omega)
      exact hasRootLine_conjugate H (coxeterWeyl K r).val hW _ _ 1 one_ne_zero
        (by simpa only [one_smul] using hstep) (ih (Nat.le_of_succ_le hk))
  intro i
  exact aux i.val (by omega)

theorem coordinate_long_coverage (K : Type) [Field K] (r : ℕ)
    (H : Subgroup ((Mat K (r + 1))ˣ)) (hW : (coxeterWeyl K r).val ∈ H)
    (h0 : HasRootLine H (coordinateLongRootMatrix K r false 0)) :
    ∀ side : Bool, ∀ i : Fin (r + 1), HasRootLine H (coordinateLongRootMatrix K r side i) := by
  have hpos := coordinate_long_side_coverage K r H hW false h0
  have hneg0 := hasRootLine_conjugate H (coxeterWeyl K r).val hW _ _ (-1 : K)
    (neg_ne_zero.mpr one_ne_zero) (coxeter_upper_longRoot_crossing K r) (hpos (Fin.last r))
  have hneg := coordinate_long_side_coverage K r H hW true hneg0
  intro side
  cases side
  · exact hpos
  · exact hneg

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
