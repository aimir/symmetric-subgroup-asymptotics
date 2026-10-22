import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNaturalPoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCell
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNumerics
import Mathlib.Algebra.CharP.CharAndCard

/-! The squared least-index bound for the SAME original odd B model.
The actual centre-one theorem is used before the cell bound, including
the rank-three field-three boundary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSquare
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexNaturalPoints
open CFSGOrthogonalBIndexCenter CFSGOrthogonalBIndexCell
open CFSGReduction PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

include p in
theorem elementary_leastProperIndex_square_lt_card (h2 : (2 : K) ≠ 0) (s ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (s + 3)) ell) :
    ell ^ 2 < Nat.card (elementaryProjective K (s + 3)) := by
  have hq : 3 ≤ Nat.card K := by
    have hn := Finite.one_lt_card (α := K)
    by_contra h
    have hc : Nat.card K = 2 := by omega
    letI := Fintype.ofFinite K
    letI oddBIndex_factTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI oddBIndex_cardTwoChar : CharP K 2 := charP_of_card_eq_prime
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    exact h2 (CharP.cast_eq_zero K 2)
  have hc := (Subgroup.center (elementaryRootGroup K (s + 3))).card_mul_index
  change Nat.card (Subgroup.center (elementaryRootGroup K (s + 3))) *
    Nat.card (elementaryProjective K (s + 3)) = Nat.card (elementaryRootGroup K (s + 3)) at hc
  have hcenter : Nat.card (Subgroup.center (elementaryRootGroup K (s + 3))) = 1 := by
    rw [center_eq_bot K p h2 (s + 2)]
    simp
  rw [hcenter, one_mul] at hc
  apply CFSGOrthogonalBIndexNumerics.index_square_lt_of_cell_lower
    (Nat.card K) (s + 3) ell _ hq (by omega)
    (elementary_leastProperIndex_mul_field_sub_one K h2 s ell hell)
  have h := elementary_card_lower K h2 (s + 2)
  rw [← hc] at h
  simpa only [Nat.add_assoc, Nat.add_sub_cancel] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSquare

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGOrthogonalBSerreMatrices

theorem typeB_odd_leastProperIndex_square_lt_card (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.B r q) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  have h := CFSGOrthogonalBIndexSquare.elementary_leastProperIndex_square_lt_card
    q.Field q.prime h2 s ell (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv] using h

end SymmetricSubgroupAsymptotics.CFSGReduction
