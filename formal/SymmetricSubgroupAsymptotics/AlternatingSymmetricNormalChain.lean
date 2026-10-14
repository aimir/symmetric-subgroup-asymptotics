import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.SimpleChiefFamilies
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! Uniform algebraic normal-chain bounds for alternating and symmetric
groups of degree at least five. These may be transported through actual
surjective representation maps; no order-based identification is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AlternatingSymmetricNormalChain

theorem alternating_normal_total {X : Type} [Fintype X] [DecidableEq X]
    (hX : 5 ≤ Nat.card X) (A B : Subgroup (alternatingGroup X))
    (hA : A.Normal) (_hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  letI := alternatingGroup.isSimpleGroup (α := X) hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A hA with h | h
  · exact Or.inl (h ▸ bot_le)
  · exact Or.inr (h ▸ le_top)

theorem symmetric_normal_classification {X : Type} [Fintype X]
    (hX : 5 ≤ Nat.card X) (N : Subgroup (Equiv.Perm X)) (hN : N.Normal) :
    N = ⊥ ∨ N = alternatingGroup X ∨ N = ⊤ := by
  by_cases hb : N = ⊥
  · exact Or.inl hb
  right
  letI := hN
  letI := alternatingGroup.isSimpleGroup (α := X) hX
  haveI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hb
  exact indexTwo_maximal (alternatingGroup X) alternatingGroup.index_eq_two N
    (Equiv.Perm.alternatingGroup_le_of_normal hX inferInstance)

theorem symmetric_normal_total {X : Type} [Fintype X]
    (hX : 5 ≤ Nat.card X) (A B : Subgroup (Equiv.Perm X))
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  rcases symmetric_normal_classification hX A hA with rfl | rfl | rfl
  · exact Or.inl bot_le
  · rcases symmetric_normal_classification hX B hB with rfl | rfl | rfl
    · exact Or.inr bot_le
    · exact Or.inl le_rfl
    · exact Or.inl le_top
  · exact Or.inr le_top

end AlternatingSymmetricNormalChain
end SymmetricSubgroupAsymptotics

end
