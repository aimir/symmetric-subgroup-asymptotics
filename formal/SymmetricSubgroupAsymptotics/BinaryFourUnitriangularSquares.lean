import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! A six-coordinate certificate for the ACTUAL upper-unitriangular subgroup
of SL4(F2). Only the 64 coordinate tuples are counted. No enumeration of GL4,
its subgroups, or affine actions is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.BinaryFourUnitriangularSquares
open CFSGUpperUnitriangular

abbrev U := upperUnitriangular (ZMod 2) 4

def coordinates (u : U) : Fin 6 → ZMod 2 :=
  ![u.val.val 0 1, u.val.val 0 2, u.val.val 0 3,
    u.val.val 1 2, u.val.val 1 3, u.val.val 2 3]

theorem matrix_eq (u : U) :
    u.val.val = !![1, coordinates u 0, coordinates u 1, coordinates u 2;
      0, 1, coordinates u 3, coordinates u 4;
      0, 0, 1, coordinates u 5;
      0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact u.property.2 _
    | exact u.property.1 (by decide)

theorem coordinates_injective : Function.Injective coordinates := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  rw [matrix_eq u, matrix_eq v, h]

/-- The literal square-one equations in the six upper entries. -/
def SquareCoordinates (x : Fin 6 → ZMod 2) : Prop :=
  x 0 * x 3 = 0 ∧ x 3 * x 5 = 0 ∧ x 0 * x 4 + x 1 * x 5 = 0

instance squareCoordinatesDecidable (x : Fin 6 → ZMod 2) : Decidable (SquareCoordinates x) :=
  inferInstanceAs (Decidable
    (x 0 * x 3 = 0 ∧ x 3 * x 5 = 0 ∧ x 0 * x 4 + x 1 * x 5 = 0))

theorem square_coordinates (u : U) (hu : u ^ 2 = 1) :
    SquareCoordinates (coordinates u) := by
  rw [pow_two] at hu
  have h02 := congrArg (fun v : U => v.val.val 0 2) hu
  have h13 := congrArg (fun v : U => v.val.val 1 3) hu
  have h03 := congrArg (fun v : U => v.val.val 0 3) hu
  change (u.val.val * u.val.val) 0 2 = 0 at h02
  change (u.val.val * u.val.val) 1 3 = 0 at h13
  change (u.val.val * u.val.val) 0 3 = 0 at h03
  rw [matrix_eq u] at h02 h13 h03
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero] at h02 h13 h03
  have hc : ∀ x : ZMod 2, x + x = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h02 - hc (coordinates u 1)
  · linear_combination h13 - hc (coordinates u 4)
  · linear_combination h03 - hc (coordinates u 2)

/-- This is a reduction on 64 six-bit tuples, not on matrix groups. -/
theorem card_square_coordinates :
    Nat.card {x : Fin 6 → ZMod 2 // SquareCoordinates x} = 28 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_square_one_le : Nat.card {u : U // u ^ 2 = 1} ≤ 28 := by
  let f : {u : U // u ^ 2 = 1} → {x : Fin 6 → ZMod 2 // SquareCoordinates x} :=
    fun u => ⟨coordinates u.val, square_coordinates u.val u.property⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    exact coordinates_injective (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective f hf).trans_eq card_square_coordinates

/-- Unitriangular matrices of this actual size have exponent dividing four. -/
theorem pow_four (u : U) : u ^ 4 = 1 := by
  have hp : u ^ 4 = (u ^ 2) ^ 2 := pow_mul u 2 2
  rw [hp, pow_two, pow_two]
  apply Subtype.ext
  apply Subtype.ext
  change (u.val.val * u.val.val) * (u.val.val * u.val.val) = 1
  rw [matrix_eq u]
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp_all only [mul_zero, add_zero, zero_add, or_true]

end SymmetricSubgroupAsymptotics.BinaryFourUnitriangularSquares
