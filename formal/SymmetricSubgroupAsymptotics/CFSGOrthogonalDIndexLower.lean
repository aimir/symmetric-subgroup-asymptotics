import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootConjugacy
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization

/-! A classification-free lower bound on the actual type-D least
proper index. The literal projective chain-root subgroup has q elements
and all nonidentity elements ambient-conjugate, so the checked Burnside
degree argument applies to every proper coset action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexLower
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexRootSubgroup
open CFSGOrthogonalDIndexRootConjugacy

theorem projective_field_card_le_proper_index (K : Type) [Field K] [Finite K]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s + 4))]
    (H : Subgroup (elementaryProjective K (s + 4))) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  letI orthogonalDIndexProjectiveFinite : Finite (elementaryProjective K (s + 4)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4))))
      (QuotientGroup.mk'_surjective _)
  let f := projectiveFirstHom K s
  have hne : f (Multiplicative.ofAdd (1 : K)) ≠ 1 := by
    intro h
    have he : Multiplicative.ofAdd (1 : K) = (1 : Multiplicative K) :=
      projectiveFirstHom_injective K s (h.trans (map_one f).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd he)
  let a : projectiveFirstRoot K s := ⟨f (Multiplicative.ofAdd (1 : K)), ⟨_, rfl⟩⟩
  have ha : a ≠ 1 := fun h => hne (congrArg Subtype.val h)
  letI orthogonalDIndexFirstRootNontrivial : Nontrivial (projectiveFirstRoot K s) := ⟨⟨a, 1, ha⟩⟩
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (projectiveFirstRoot K s) (projectiveFirst_nonidentity_conjugate K s) H hH
  rwa [projectiveFirstRoot_card K s] at hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexLower

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_order_le_leastProperIndex (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) : q.order ≤ ell := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  let e : CFSG.Models.D (s + 4) q ≃* elementaryProjective q.Field (s + 4) :=
    serreProjectiveEquivElementaryProjective q.Field s
  letI orthogonalDIndexElementaryProjectiveSimple : IsSimpleGroup (elementaryProjective q.Field (s + 4)) :=
    e.symm.isSimpleGroup
  obtain ⟨H, hH, hi⟩ := (leastProperIndex_of_mulEquiv e ell hell).1
  have hh := CFSGOrthogonalDIndexLower.projective_field_card_le_proper_index q.Field s H hH
  simpa only [q.card_field, hi] using hh

end SymmetricSubgroupAsymptotics.CFSGReduction
