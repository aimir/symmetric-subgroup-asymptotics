import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryTranspose
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalFixedSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Actual defining-fixed natural matrices have no common nonzero vector.
For rank>=2 the checked upper radical and one actual inverse-transposed
central element suffice. Rank1 is handled by its two literal root units.
This supplies a concrete hypothesis for the difference-span criterion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists CFSGSerreSquareZeroMatrix

theorem naturalFixed_no_fixed_vectors_shift (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2)
    (hx : ∀ g : naturalFixed (s + 2) q, (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = x) :
    x = 0 := by
  have hu : ∀ g : naturalUnipotent (s + 2) q,
      (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = x :=
    fun g => hx ⟨g.val, g.property.2⟩
  obtain ⟨hm, hl⟩ := (naturalUnipotent_fixed_iff q s x).mp hu
  obtain ⟨t, ht, htc⟩ := exists_nonzero_central_parameter q s
  let u := radicalElement q s 0 t htc
  let a : naturalFixed (s + 2) q := ⟨u.val, u.property.2⟩
  let b := fixedInverseTransposeHom q (s + 2) a
  have hmat : (b.val.val : Mat (q.Extension 2) (s + 2)) =
      Matrix.reindex (splitEquiv s) (splitEquiv s)
        ((upperArray (0 : Fin (s + 1) → q.Extension 2) 0 (-t)).transpose) := by
    change (↑((naturalUpperUnit (q.Extension 2) s (firstRow q s 0) 0 t)⁻¹) :
      Mat (q.Extension 2) (s + 2)).transpose = _
    rw [firstRow_zero]
    change (Matrix.reindex (splitEquiv s) (splitEquiv s)
      (upperArray (-(0 : Fin (s + 1) → q.Extension 2)) (-0)
        (-t + dotProduct (0 : Fin (s + 1) → q.Extension 2) 0))).transpose = _
    simp only [neg_zero, zero_dotProduct, add_zero, Matrix.transpose_reindex]
  have he := congrArg (fun y : Fin (s + 3) → q.Extension 2 =>
    y (splitEquiv s (.inr (.inr ())))) (hx b)
  dsimp only at he
  rw [hmat, reindex_mulVec_apply] at he
  have he' : -t * x 0 + x (Fin.last (s + 2)) = x (Fin.last (s + 2)) := by
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.transpose_apply,
      upperArray, Function.comp_apply, splitEquiv, splitIndex] using he
  have h0 : x 0 = 0 := (mul_eq_zero.mp (add_eq_right.mp he')).resolve_left (neg_ne_zero.mpr ht)
  funext i
  obtain ⟨z, rfl⟩ := (splitEquiv s).surjective i
  rcases z with v | (j | v)
  · cases v; exact h0
  · exact hm j
  · cases v; exact hl

def rankOneFixedRoot (q : CFSG.PrimePower) (neg : Bool) : naturalFixed 1 q :=
  ⟨elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) neg 0 1, by
    change diagramFieldUnitHom (q.Extension 2) 1 (definingFieldAutomorphism q 2).toRingHom
      (naturalRootUnit (q.Extension 2) 1 neg 0 1) = naturalRootUnit (q.Extension 2) 1 neg 0 1
    rw [CFSGTwistedA2UnitRootTwist.simpleUnit_twist, map_one]
    rfl⟩

theorem naturalFixed_no_fixed_vectors_one (q : CFSG.PrimePower)
    (x : Fin 2 → q.Extension 2)
    (hx : ∀ g : naturalFixed 1 q, (g.val.val : Mat (q.Extension 2) 1) *ᵥ x = x) : x = 0 := by
  have hp := congrArg (fun y : Fin 2 → q.Extension 2 => y 0) (hx (rankOneFixedRoot q false))
  have hn := congrArg (fun y : Fin 2 → q.Extension 2 => y 1) (hx (rankOneFixedRoot q true))
  have hp' : x 0 + x 1 = x 0 := by
    simpa [rankOneFixedRoot, elementaryRoot, naturalRootUnit, rootMatrix, positive,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply] using hp
  have hn' : x 1 + x 0 = x 1 := by
    simpa [rankOneFixedRoot, elementaryRoot, naturalRootUnit, rootMatrix, negative, positive,
      Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, add_comm] using hn
  have h0 : x 0 = 0 := add_eq_left.mp hn'
  have h1 : x 1 = 0 := add_eq_left.mp hp'
  funext i
  fin_cases i <;> assumption

theorem naturalFixed_no_fixed_vectors (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (x : Fin (r + 1) → q.Extension 2)
    (hx : ∀ g : naturalFixed r q, (g.val.val : Mat (q.Extension 2) r) *ᵥ x = x) : x = 0 := by
  rcases r with _ | (_ | s)
  · omega
  · exact naturalFixed_no_fixed_vectors_one q x hx
  · exact naturalFixed_no_fixed_vectors_shift q s x hx

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
