import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPointAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original type-D least proper index is bounded above by all
natural projective points. Only an actual moved point and the scalar
centre are used, not a singular-orbit count or classical recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUpper
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPointAction
open PrimitiveSocleRawStructure CFSGReduction
variable (K : Type) [Field K] [Finite K]

theorem naturalPoints_card_mul_units (r : ℕ) :
    Nat.card (NaturalPoints K r) * (Nat.card K - 1) = Nat.card K ^ (2 * r) - 1 := by
  simpa only [NaturalPoints, Nat.card_fun, Nat.card_sum, Nat.card_fin, two_mul]
    using (Projectivization.card K (Index r → K)).symm

theorem elementary_leastProperIndex_le_naturalPoints (s ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (s + 4)) ell) :
    ell ≤ Nat.card (NaturalPoints K (s + 4)) := by
  obtain ⟨H, hH, hindex⟩ := exists_proper_subgroup_of_natural_point_index K s
  exact (hell.2 H hH).trans hindex

theorem elementary_leastProperIndex_mul_field_sub_one (s ell : ℕ)
    (hell : LeastProperIndex (elementaryProjective K (s + 4)) ell) :
    ell * (Nat.card K - 1) ≤ Nat.card K ^ (2 * (s + 4)) - 1 :=
  (Nat.mul_le_mul_right (Nat.card K - 1)
    (elementary_leastProperIndex_le_naturalPoints K s ell hell)).trans_eq
      (naturalPoints_card_mul_units K (s + 4))

theorem serreTypeD_leastProperIndex_mul_field_sub_one (s ell : ℕ)
    [IsSimpleGroup (CFSG.Models.Chevalley.Projective (CartanMatrix.D (s + 4)) K)]
    (hell : LeastProperIndex (CFSG.Models.Chevalley.Projective (CartanMatrix.D (s + 4)) K) ell) :
    ell * (Nat.card K - 1) ≤ Nat.card K ^ (2 * (s + 4)) - 1 :=
  elementary_leastProperIndex_mul_field_sub_one K s ell
    (leastProperIndex_of_mulEquiv (serreProjectiveEquivElementaryProjective K s) ell hell)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUpper

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeD_leastProperIndex_mul_field_sub_one (r : ℕ) (hr : 4 ≤ r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.D r q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.D r q) ell) :
    ell * (q.order - 1) ≤ q.order ^ (2 * r) - 1 := by
  have he : r - 4 + 4 = r := by omega
  letI : IsSimpleGroup (CFSG.Models.D (r - 4 + 4) q) := by rw [he]; infer_instance
  have hell' : LeastProperIndex (CFSG.Models.D (r - 4 + 4) q) ell := by rw [he]; exact hell
  have h := CFSGOrthogonalDIndexUpper.serreTypeD_leastProperIndex_mul_field_sub_one
    q.Field (r - 4) ell hell'
  simpa only [he, q.card_field] using h

end SymmetricSubgroupAsymptotics.CFSGReduction
