import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Three cyclically permuted binary coordinates

The degree-six binary-block owner charts its block kernel inside `F₂^3`,
and an element over a three-cycle of the blocks shifts the coordinates.
This file records the finitely many coordinate facts used by the quotient
counting argument.  Every statement is closed and decided by evaluation.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The cyclic shift `0 ↦ 1 ↦ 2 ↦ 0` of the three block coordinates. -/
def rotThree : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- A nonidentity element of order three is the inverse shift or its
square. -/
theorem rotThree_inv_of_order_three :
    ∀ g : Equiv.Perm (Fin 3), g ≠ 1 → g ^ 3 = 1 →
      g = rotThree⁻¹ ∨ g ^ 2 = rotThree⁻¹ := by
  decide

theorem rotThree_inv_ne_one : rotThree⁻¹ ≠ 1 := by decide

/-- The first coordinate of the three shifts detects every vector. -/
theorem rotThree_detect : ∀ v : Fin 3 → ZMod 2,
    v 0 = 0 → v (rotThree 0) = 0 → v (rotThree (rotThree 0)) = 0 → v = 0 := by
  decide

/-- The first difference of the three shifts detects every vector modulo
the diagonal. -/
theorem rotThree_pair_detect : ∀ v : Fin 3 → ZMod 2,
    v 0 + v (rotThree 0) = 0 →
    v (rotThree 0) + v (rotThree (rotThree 0)) = 0 →
    v (rotThree (rotThree 0)) + v (rotThree (rotThree (rotThree 0))) = 0 →
    v = 0 ∨ v = fun _ => 1 := by
  decide

/-- The two nontrivial shifts add to the vector plus its coordinate sum on
the diagonal. -/
theorem rotThree_trace : ∀ (v : Fin 3 → ZMod 2) (i : Fin 3),
    v (rotThree i) + v (rotThree (rotThree i)) = v i + (v 0 + v 1 + v 2) := by
  decide

/-- Any vector off the diagonal generates, with its shifts, every first
difference `v ∘ rotThree + v`. -/
theorem rotThree_generate : ∀ s v : Fin 3 → ZMod 2, s ≠ 0 → s ≠ (fun _ => 1) →
    ∃ a b c : ZMod 2, ∀ i : Fin 3,
      v (rotThree i) + v i =
        a * s i + b * s (rotThree i) + c * s (rotThree (rotThree i)) := by
  decide

theorem binaryThree_add_self : ∀ v : Fin 3 → ZMod 2, v + v = 0 := by
  decide

theorem zmodTwo_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

theorem zmodTwo_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

end SymmetricSubgroupAsymptotics
