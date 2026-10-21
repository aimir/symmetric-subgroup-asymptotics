import SymmetricSubgroupAsymptotics.CFSGSymplecticShortRootConjugacy
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization

/-! A classification-free lower bound on the literal least proper
index of every actual simple C model. The short-root group has order
q and one nonidentity ambient conjugacy class, hence every proper
coset action has degree at least q. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem projective_field_card_le_proper_index (K : Type) [Field K] [Finite K]
    (r : ℕ) (hr : 0 < r) [IsSimpleGroup (elementaryProjective K (r + 1))]
    (H : Subgroup (elementaryProjective K (r + 1))) (hH : H ≠ ⊤) :
    Nat.card K ≤ H.index := by
  let f := projectiveShortHom K r
  have hne : f (Multiplicative.ofAdd (1 : K)) ≠ 1 := by
    intro h
    have he : Multiplicative.ofAdd (1 : K) = (1 : Multiplicative K) :=
      projectiveShortHom_injective K r hr (h.trans (map_one f).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd he)
  let a : projectiveShortRoot K r := ⟨f (Multiplicative.ofAdd (1 : K)), ⟨_, rfl⟩⟩
  have ha : a ≠ 1 := fun h => hne (congrArg Subtype.val h)
  letI projectiveShortRootNontrivial : Nontrivial (projectiveShortRoot K r) := ⟨⟨a, 1, ha⟩⟩
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (projectiveShortRoot K r) (projectiveShort_nonidentity_conjugate K r hr) H hH
  rwa [projectiveShortRoot_card K r hr] at hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_order_le_leastProperIndex (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C r q) ell) : q.order ≤ ell := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
  let e : CFSG.Models.C (s + 2) q ≃* elementaryProjective q.Field (s + 2) :=
    serreProjectiveEquivElementaryProjective q.Field (s + 1)
  letI elementaryProjectiveSimple : IsSimpleGroup (elementaryProjective q.Field (s + 2)) :=
    e.symm.isSimpleGroup
  obtain ⟨H, hH, hi⟩ := (leastProperIndex_of_mulEquiv e ell hell).1
  have hh := projective_field_card_le_proper_index q.Field (s + 1) (by omega) H hH
  simpa only [q.card_field, hi] using hh

end SymmetricSubgroupAsymptotics.CFSGReduction
