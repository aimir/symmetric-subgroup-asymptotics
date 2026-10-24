import SymmetricSubgroupAsymptotics.CFSGUnitaryGeneralVectorMiddleClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositePivot
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralLineAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorus

/-! Actual determinant-one unitary words normalize an arbitrary nonzero
natural vector to (a,0,...,0,1). No isometry extension or transitivity
premise is used, and the natural vector dimension is at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

theorem exists_natural_first_line_scale (q : CFSG.PrimePower) (s : ℕ)
    (a : q.Extension 2) (ha : a ≠ 0) :
    ∃ g : naturalFixed (s + 2) q,
      ∀ i, (g.val.val : Mat (q.Extension 2) (s + 2)) i 0 = if i = 0 then a else 0 := by
  cases s with
  | zero =>
    refine ⟨rankTwoNaturalTorus q (Units.mk0 a ha), ?_⟩
    intro i
    rw [rankTwoNaturalTorus_matrix]
    by_cases hi : i = 0
    · subst i
      rw [Matrix.diagonal_apply, if_pos rfl]
      rfl
    · simp only [Matrix.diagonal_apply, if_neg hi]
  | succ t =>
    refine ⟨pairedTorus q t a, ?_⟩
    intro i
    have he := pairedTorus_first_axis q t a 1 ha
    rw [Matrix.mulVec_single_one, mul_one] at he
    simpa only [Pi.single_apply] using congrFun he i

theorem natural_first_line_inverse_last (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) (a : q.Extension 2)
    (hcol : ∀ i, (g.val.val : Mat (q.Extension 2) r) i 0 = if i = 0 then a else 0)
    (x : Fin (r + 1) → q.Extension 2) :
    (((g⁻¹).val.val : Mat (q.Extension 2) r) *ᵥ x) (Fin.last r) =
      definingFieldAutomorphism q 2 a * x (Fin.last r) := by
  have hform := fixed_unit_signedForm (q.Extension 2) r
    (definingFieldAutomorphism q 2).toRingHom g.val.val g.property
  have hrow := isometric_inverse_last_row r (definingFieldAutomorphism q 2)
    g.val.val a hform hcol
  change (((↑(g.val.val⁻¹) : Mat (q.Extension 2) r) *ᵥ x) (Fin.last r)) = _
  simp [Matrix.mulVec, dotProduct, hrow]

theorem exists_natural_last_eq_one (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0) :
    ∃ g : naturalFixed (s + 2) q,
      ((g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x) (Fin.last (s + 2)) = 1 := by
  obtain ⟨h, _, hh⟩ := exists_opposite_last_ne_zero q s x hx
  let y := (h.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x
  let a := (definingFieldAutomorphism q 2 (y (Fin.last (s + 2))))⁻¹
  have ha : a ≠ 0 := inv_ne_zero ((map_ne_zero _).mpr hh)
  obtain ⟨t, ht⟩ := exists_natural_first_line_scale q s a ha
  refine ⟨t⁻¹ * h, ?_⟩
  change ((((t⁻¹).val.val : Mat (q.Extension 2) (s + 2)) *
    (h.val.val : Mat (q.Extension 2) (s + 2))) *ᵥ x) (Fin.last (s + 2)) = 1
  rw [← Matrix.mulVec_mulVec]
  change (((t⁻¹).val.val : Mat (q.Extension 2) (s + 2)) *ᵥ y) (Fin.last (s + 2)) = 1
  rw [natural_first_line_inverse_last q (s + 2) t a ht]
  dsimp only [a]
  have hσσ : definingFieldAutomorphism q 2
      (definingFieldAutomorphism q 2 (y (Fin.last (s + 2)))) = y (Fin.last (s + 2)) :=
    extension_two_pow_twice q _
  rw [map_inv₀, hσσ, inv_mul_cancel₀ hh]

theorem exists_natural_two_axis_normal_form (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0) :
    ∃ (g : naturalFixed (s + 2) q) (a : q.Extension 2),
      (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x =
        Pi.single 0 a + Pi.single (Fin.last (s + 2)) 1 := by
  obtain ⟨h, hh⟩ := exists_natural_last_eq_one q s x hx
  let y := (h.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x
  have hyone : y (Fin.last (s + 2)) = 1 := hh
  have hy : y (Fin.last (s + 2)) ≠ 0 := by rw [hyone]; exact one_ne_zero
  obtain ⟨u, a, hu⟩ := exists_natural_radical_clear_middle q s y hy
  let U : naturalFixed (s + 2) q := ⟨u.val, u.property.2⟩
  refine ⟨U * h, a, ?_⟩
  change ((u.val.val : Mat (q.Extension 2) (s + 2)) *
    (h.val.val : Mat (q.Extension 2) (s + 2))) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec]
  change (u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ y = _
  rw [hu, hyone]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
