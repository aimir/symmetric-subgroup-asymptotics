import SymmetricSubgroupAsymptotics.S8Sylow128DoubleCosets
import Mathlib.Data.Fin.VecNotation

/-! Selected literal candidate overgroups of original8T35. The row
definitions retain the actual seed and double-coset root. This file makes
no completeness or join-closure claim. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Sylow128LiteralModels
open S8Sylow128LeftCosets

def anchors : Fin 4 → Fin 16 := ![0, 5, 6, 1]

def generators (i : Fin 4) : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Sylow128DoubleCosets.roots (anchors i)))
    BinaryMenuCayley8T35.generators

def rows (i : Fin 4) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem rows_eq_adjoin (i : Fin 4) : rows i =
    H ⊔ Subgroup.closure
      {representatives (S8Sylow128DoubleCosets.roots (anchors i))} := by
  simp only [rows, generators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem contains_seed (i : Fin 4) : H ≤ rows i := by
  rw [rows_eq_adjoin]
  exact le_sup_left

theorem row_zero : rows 0 = H := by
  rw [rows_eq_adjoin]
  have h : representatives (S8Sylow128DoubleCosets.roots (anchors 0)) = 1 := by
    decide +kernel
  rw [h]
  simp

end SymmetricSubgroupAsymptotics.S8Sylow128LiteralModels
end
