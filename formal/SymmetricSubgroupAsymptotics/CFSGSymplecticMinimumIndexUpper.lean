import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectivePointIndex
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual original type-C least proper index is at most the
number of natural projective points. The upper bound needs only one
moved point, not a full symplectic-group identification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open PrimitiveSocleRawStructure CFSGReduction
variable (K : Type) [Field K] [Finite K]

theorem naturalPoints_card_mul_units (r : ℕ) :
    Nat.card (NaturalPoints K r) * (Nat.card K - 1) =
      Nat.card K ^ (2 * r) - 1 := by
  simpa only [NaturalPoints, Nat.card_fun, Nat.card_sum, Nat.card_fin, two_mul]
    using (Projectivization.card K (Index r → K)).symm

theorem elementary_leastProperIndex_le_naturalPoints (r ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (r + 1)) ell) :
    ell ≤ Nat.card (NaturalPoints K (r + 1)) := by
  obtain ⟨H, hH, hindex⟩ := exists_proper_subgroup_of_natural_point_index K r
  exact (hell.2 H hH).trans hindex

theorem serreTypeC_leastProperIndex_mul_field_sub_one (r ell : ℕ)
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective
      (CartanMatrix.C (r + 1)).transpose K)]
    (hell : LeastProperIndex (CFSG.Models.Chevalley.Projective
      (CartanMatrix.C (r + 1)).transpose K) ell) :
    ell * (Nat.card K - 1) ≤ Nat.card K ^ (2 * (r + 1)) - 1 := by
  have h := elementary_leastProperIndex_le_naturalPoints K r ell
    (leastProperIndex_of_mulEquiv (serreProjectiveEquivElementaryProjective K r) ell hell)
  exact (Nat.mul_le_mul_right (Nat.card K - 1) h).trans_eq
    (naturalPoints_card_mul_units K (r + 1))

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeC_leastProperIndex_mul_field_sub_one (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.C r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.C r q) ell) :
    ell * (q.order - 1) ≤ q.order ^ (2 * r) - 1 := by
  have he : r - 1 + 1 = r := by omega
  letI : IsSimpleGroup (CFSG.Models.Chevalley.Projective
      (CartanMatrix.C (r - 1 + 1)).transpose q.Field) := by
    rw [he]
    infer_instance
  have hell' : LeastProperIndex (CFSG.Models.Chevalley.Projective
      (CartanMatrix.C (r - 1 + 1)).transpose q.Field) ell := by
    rw [he]
    exact hell
  have h := CFSGSymplecticSerreMatrices.serreTypeC_leastProperIndex_mul_field_sub_one
    q.Field (r - 1) ell hell'
  simpa only [he, q.card_field] using h

end SymmetricSubgroupAsymptotics.CFSGReduction
