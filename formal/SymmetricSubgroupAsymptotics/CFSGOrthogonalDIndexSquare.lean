import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCell
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexScalarNumerics
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCenterCard
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUpper
import Mathlib.FieldTheory.Finite.Basic

/-! The actual original type-D squared least-index bound in all ranks
at least four and all finite fields. A literal alternating block cell,
coarse scalar centre injection and an actual point stabilizer suffice;
no full orthogonal recognition or order formula is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexCell CFSGOrthogonalDIndexCenterCard CFSGOrthogonalDIndexUpper
open PrimitiveSocleRawStructure CFSGReduction
variable (K : Type) [Field K] [Finite K]

theorem elementary_leastProperIndex_square_lt_card (s ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (s + 4)) ell) :
    ell ^ 2 < Nat.card (elementaryProjective K (s + 4)) := by
  apply CFSGOrthogonalDIndexScalarNumerics.index_square_lt_of_cell_lower
    (Nat.card K) (s + 4) (Nat.card (EntryIndex (s + 4))) ell
    (Nat.card (Subgroup.center (elementaryRootGroup K (s + 4))))
    (Nat.card (elementaryProjective K (s + 4)))
    (by have h := Finite.one_lt_card (α := K); omega) (by omega)
    (entryIndex_card_twice (s + 4)) ?_
    (elementary_leastProperIndex_mul_field_sub_one K s ell hell)
    (triangular_projective_cell_card_lower K s)
  exact (center_card_le_field K s).trans (Nat.le_self_pow (by decide : 2 ≠ 0) (Nat.card K))

theorem serreTypeD_leastProperIndex_square_lt_card (s ell : ℕ)
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective (CartanMatrix.D (s + 4)) K)]
    (hell : LeastProperIndex (CFSG.Models.Chevalley.Projective (CartanMatrix.D (s + 4)) K) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.Chevalley.Projective (CartanMatrix.D (s + 4)) K) := by
  let e := serreProjectiveEquivElementaryProjective K s
  have h := elementary_leastProperIndex_square_lt_card K s ell
    (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeD_leastProperIndex_square_lt_card (r : ℕ) (q : CFSG.PrimePower)
    (hr : 4 ≤ r) [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.D r q) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  exact CFSGOrthogonalDIndexSquare.serreTypeD_leastProperIndex_square_lt_card
    q.Field s ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
