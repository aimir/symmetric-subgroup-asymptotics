import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarConjugacy
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization

/-! The stronger actual type-D index lower bound q^(r-1). The root
star is an original q^(r-1)-element abelian subgroup with all nonidentity
members ambient-conjugate. No alternate action or classical-group
identification is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarLower
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexStarSubgroup
open CFSGOrthogonalDIndexStarConjugacy

theorem projective_field_power_le_proper_index (K : Type) [Field K] [Finite K]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s + 4))]
    (H : Subgroup (elementaryProjective K (s + 4))) (hH : H ≠ ⊤) :
    Nat.card K ^ (s + 3) ≤ H.index := by
  letI orthogonalDIndexStarProjectiveFinite : Finite (elementaryProjective K (s + 4)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4))))
      (QuotientGroup.mk'_surjective _)
  letI orthogonalDIndexStarRootNontrivial : Nontrivial (starRoot K s) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [starRoot_card]
      exact Nat.one_lt_pow (by omega) (Finite.one_lt_card (α := K)))
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (starRoot K s) (star_nonidentity_conjugate K s) H hH
  rwa [starRoot_card K s] at hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarLower

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_order_power_le_leastProperIndex (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) : q.order ^ (r - 1) ≤ ell := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  let e : CFSG.Models.D (s + 4) q ≃* elementaryProjective q.Field (s + 4) :=
    serreProjectiveEquivElementaryProjective q.Field s
  letI orthogonalDIndexStarProjectiveSimple : IsSimpleGroup (elementaryProjective q.Field (s + 4)) :=
    e.symm.isSimpleGroup
  obtain ⟨H, hH, hi⟩ := (leastProperIndex_of_mulEquiv e ell hell).1
  have hh := CFSGOrthogonalDIndexStarLower.projective_field_power_le_proper_index q.Field s H hH
  simpa only [q.card_field, show s + 4 - 1 = s + 3 by omega, hi] using hh

end SymmetricSubgroupAsymptotics.CFSGReduction
