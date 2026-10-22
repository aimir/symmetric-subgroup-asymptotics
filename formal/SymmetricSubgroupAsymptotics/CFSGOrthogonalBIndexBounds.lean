import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSquare

/-! Exact lower, upper and squared least-index consequences for original
odd B models. This file makes no claim about their outer automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGOrthogonalBSerreMatrices

theorem typeB_odd_order_le_leastProperIndex (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) : q.order ≤ ell := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  letI oddBIndexBounds_projectiveSimple : IsSimpleGroup (elementaryProjective q.Field (s + 3)) :=
    e.symm.isSimpleGroup
  obtain ⟨H, hH, hi⟩ := (leastProperIndex_of_mulEquiv e ell hell).1
  have h := CFSGOrthogonalBIndexRootSubgroup.field_card_le_proper_index q.Field h2 s H hH
  simpa only [q.card_field, hi] using h

theorem typeB_odd_leastProperIndex_mul_field_sub_one (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    ell * (q.order - 1) ≤ q.order ^ (2 * r + 1) - 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  have h := CFSGOrthogonalBIndexNaturalPoints.elementary_leastProperIndex_mul_field_sub_one
    q.Field h2 s ell (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [q.card_field] using h

theorem typeB_odd_leastProperIndex_bounds (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    q.order ≤ ell ∧ ell ^ 2 < Nat.card (CFSG.Models.B r q) :=
  ⟨typeB_odd_order_le_leastProperIndex r hr q h2 ell hell,
    typeB_odd_leastProperIndex_square_lt_card r hr q h2 ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
