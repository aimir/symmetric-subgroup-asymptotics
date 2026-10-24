import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySmallIsotropicVectors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Actual fixed-field determinant-one matrices act on the literal
two-dimensional unitary middle space. Arbitrary nonzero fixed-field
columns occur. A vector of nonzero signed norm has trivial stabilizer;
no global SU2 norm-shell transitivity is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

theorem rankOneScalarHom_fixed (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q)) :
    rankOneScalarHom q A ∈ naturalFixed 1 q := by
  apply Units.ext
  change (diagramFieldUnitHom (q.Extension 2) 1 (definingFieldAutomorphism q 2).toRingHom
    (rankOneScalarHom q A).val : Mat (q.Extension 2) 1) =
      ((rankOneScalarHom q A).val : Mat (q.Extension 2) 1)
  rw [rank_one_diagramField_val]
  ext i j
  change definingFieldAutomorphism q 2 ((A.val i j : rankOneFixedField q) : q.Extension 2) =
    ((A.val i j : rankOneFixedField q) : q.Extension 2)
  exact (A.val i j).property

def rankOneScalarFixedHom (q : CFSG.PrimePower) :
    Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q) →* naturalFixed 1 q :=
  (rankOneScalarHom q).codRestrict (naturalFixed 1 q) (rankOneScalarHom_fixed q)

theorem rankOneScalarFixedHom_matrix (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q)) :
    ((rankOneScalarFixedHom q A).val.val : Mat (q.Extension 2) 1) =
      A.val.map (rankOneFixedField q).subtype := rfl

theorem exists_rankOneFixed_first_column (q : CFSG.PrimePower)
    (x : Fin 2 → rankOneFixedField q) (hx : x ≠ 0) :
    ∃ g : naturalFixed 1 q, ∀ i : Fin 2,
      (g.val.val : Mat (q.Extension 2) 1) i 0 = (x i : q.Extension 2) := by
  by_cases h0 : x 0 ≠ 0
  · let A : Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q) :=
      ⟨!![x 0,0; x 1,(x 0)⁻¹], by
        rw [Matrix.det_fin_two]
        simp [h0]⟩
    refine ⟨rankOneScalarFixedHom q A, ?_⟩
    intro i
    rw [rankOneScalarFixedHom_matrix]
    fin_cases i <;> rfl
  · have hx0 : x 0 = 0 := by simpa using h0
    have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      ext i
      fin_cases i <;> simp [hx0, h1]
    let A : Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q) :=
      ⟨!![0,-(x 1)⁻¹; x 1,0], by
        rw [Matrix.det_fin_two]
        simp [h1]⟩
    refine ⟨rankOneScalarFixedHom q A, ?_⟩
    intro i
    rw [rankOneScalarFixedHom_matrix]
    fin_cases i
    · exact congrArg Subtype.val hx0.symm
    · rfl

private theorem fixed_coefficients_zero_of_norm_ne_zero (q : CFSG.PrimePower)
    (v : Fin 2 → q.Extension 2) (hv : unitaryNaturalPair q 1 v v ≠ 0)
    (a b : q.Extension 2)
    (ha : definingFieldAutomorphism q 2 a = a) (hb : definingFieldAutomorphism q 2 b = b)
    (hs : a * v 0 + b * v 1 = 0) : a = 0 ∧ b = 0 := by
  have hn : definingFieldAutomorphism q 2 (v 0) * v 1 -
      definingFieldAutomorphism q 2 (v 1) * v 0 ≠ 0 := by
    simpa only [rank_one_pair_formula] using hv
  have ht := congrArg (definingFieldAutomorphism q 2) hs
  simp only [map_add, map_mul, map_zero, ha, hb] at ht
  have hA : a * (definingFieldAutomorphism q 2 (v 0) * v 1 -
      definingFieldAutomorphism q 2 (v 1) * v 0) = 0 := by
    linear_combination v 1 * ht - definingFieldAutomorphism q 2 (v 1) * hs
  have hB : b * (definingFieldAutomorphism q 2 (v 0) * v 1 -
      definingFieldAutomorphism q 2 (v 1) * v 0) = 0 := by
    linear_combination definingFieldAutomorphism q 2 (v 0) * hs - v 0 * ht
  exact ⟨(mul_eq_zero.mp hA).resolve_right hn, (mul_eq_zero.mp hB).resolve_right hn⟩

theorem rankOne_nonisotropic_action_injective (q : CFSG.PrimePower)
    (v : Fin 2 → q.Extension 2) (hv : unitaryNaturalPair q 1 v v ≠ 0) :
    Function.Injective (fun g : naturalFixed 1 q => (g.val.val : Mat (q.Extension 2) 1) *ᵥ v) := by
  intro g h he
  have hrow (i : Fin 2) :
      (g.val.val : Mat (q.Extension 2) 1) i 0 = (h.val.val : Mat (q.Extension 2) 1) i 0 ∧
      (g.val.val : Mat (q.Extension 2) 1) i 1 = (h.val.val : Mat (q.Extension 2) 1) i 1 := by
    have hi := congrFun he i
    change (∑ j : Fin 2, (g.val.val : Mat (q.Extension 2) 1) i j * v j) =
      (∑ j : Fin 2, (h.val.val : Mat (q.Extension 2) 1) i j * v j) at hi
    simp only [Fin.sum_univ_two] at hi
    have hc := fixed_coefficients_zero_of_norm_ne_zero q v hv
      ((g.val.val : Mat (q.Extension 2) 1) i 0 - (h.val.val : Mat (q.Extension 2) 1) i 0)
      ((g.val.val : Mat (q.Extension 2) 1) i 1 - (h.val.val : Mat (q.Extension 2) 1) i 1)
      (by rw [map_sub, rank_one_fixed_entry, rank_one_fixed_entry])
      (by rw [map_sub, rank_one_fixed_entry, rank_one_fixed_entry])
      (by linear_combination hi)
    exact ⟨sub_eq_zero.mp hc.1, sub_eq_zero.mp hc.2⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases j
  · exact (hrow i).1
  · exact (hrow i).2

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
