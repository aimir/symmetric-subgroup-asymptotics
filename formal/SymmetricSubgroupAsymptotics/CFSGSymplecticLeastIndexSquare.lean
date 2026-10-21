import SymmetricSubgroupAsymptotics.CFSGSymplecticAugmentedCell
import SymmetricSubgroupAsymptotics.CFSGSymplecticCellIndexNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimumIndexUpper
import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterCardinality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.CharAndCard

/-! The squared least-index bound for the actual original C models.
One augmented symmetric cell covers all permitted ranks and fields. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open PrimitiveSocleRawStructure CFSGReduction CFSGSymplecticCellIndexNumerics
variable (K : Type) [Field K] [Finite K]

theorem elementary_leastProperIndex_square_lt_card (r : ℕ) (hr : 0 < r)
    (hs : r + 1 = 2 → Nat.card K ≠ 2) (ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (r + 1)) ell) :
    ell ^ 2 < Nat.card (elementaryProjective K (r + 1)) := by
  apply index_square_lt_of_cell_lower (Nat.card K) (r + 1) ell
    (Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))))
    (Nat.card (elementaryProjective K (r + 1)))
    (by have h := Finite.one_lt_card (α := K); omega) (by omega) hs
    (center_card_le_two K r) ?_ ?_ ?_
  · intro hq
    letI := Fintype.ofFinite K
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : CharP K 2 := charP_of_card_eq_prime
      (by simpa only [Nat.card_eq_fintype_card] using hq)
    rw [center_eq_bot_of_char_two K r]
    simp
  · have h := elementary_leastProperIndex_le_naturalPoints K r ell hell
    exact (Nat.mul_le_mul_right (Nat.card K - 1) h).trans_eq
      (naturalPoints_card_mul_units K (r + 1))
  · simpa only [Nat.add_assoc] using augmentedCell_projective_card_lower K r hr

theorem serreTypeC_leastProperIndex_square_lt_card (r : ℕ) (hr : 0 < r)
    (hs : r + 1 = 2 → Nat.card K ≠ 2)
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective (CartanMatrix.C (r + 1)).transpose K)]
    (ell : ℕ) (hell : LeastProperIndex
      (CFSG.Models.Chevalley.Projective (CartanMatrix.C (r + 1)).transpose K) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.Chevalley.Projective
      (CartanMatrix.C (r + 1)).transpose K) := by
  let e := serreProjectiveEquivElementaryProjective K r
  have h := elementary_leastProperIndex_square_lt_card K r hr hs ell
    (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeC_leastProperIndex_square_lt_card (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2 ≤ r) (hs : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.C r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C r q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.C r q) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  apply CFSGSymplecticSerreMatrices.serreTypeC_leastProperIndex_square_lt_card
    q.Field s (by omega) ?_ ell hell
  intro h
  rw [q.card_field]
  exact hs h

end SymmetricSubgroupAsymptotics.CFSGReduction
