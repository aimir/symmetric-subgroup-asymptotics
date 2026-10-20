import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-!
# Two normal generators from two checked registry transitions

Two transitions from the bottom state adjoin the normal closures of two
class representatives. A small reachability witness for each state therefore
certifies a uniform two-generator bound for the complete normal registry.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A two-position tuple normally generates the join of the individual
normal closures. -/
theorem normalClosure_pair_tuple {G : Type} [Group G] (x y : G) :
    Subgroup.normalClosure (Set.range ![x, y]) =
      Subgroup.normalClosure ({x} : Set G) ⊔
        Subgroup.normalClosure ({y} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.mem_sup_left (Subgroup.subset_normalClosure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_normalClosure (by simp))
  · apply sup_le
    · apply Subgroup.normalClosure_le_normal
      intro z hz
      have hz : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 2))
    · apply Subgroup.normalClosure_le_normal
      intro z hz
      have hz : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact Subgroup.subset_normalClosure (Set.mem_range_self (1 : Fin 2))

namespace FiniteNormalJoinRegistry

/-- A registry in which every state is reached from bottom in two steps
supplies two ambient normal generators for every normal subgroup. -/
theorem normal_generating_pair
    {G I : Type} [Group G] [Finite G] {c : ℕ}
    {representative : Fin c → G} {states : I → Subgroup G}
    {C : FiniteConjugacyCardinalCover representative}
    (R : FiniteNormalJoinRegistry C states)
    (hreach : ∀ i, ∃ a b, R.child (R.child R.bottom a) b = i)
    (N : Subgroup G) [N.Normal] :
    ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨i, rfl⟩ := R.complete N
  obtain ⟨a, b, hab⟩ := hreach i
  refine ⟨![representative a, representative b], ?_⟩
  calc
    Subgroup.normalClosure (Set.range ![representative a, representative b]) =
        Subgroup.normalClosure ({representative a} : Set G) ⊔
          Subgroup.normalClosure ({representative b} : Set G) :=
      normalClosure_pair_tuple _ _
    _ = states (R.child (R.child R.bottom a) b) := by
      rw [R.child_eq, R.child_eq, R.bottom_eq, bot_sup_eq]
    _ = states i := congrArg states hab

end FiniteNormalJoinRegistry
end SymmetricSubgroupAsymptotics

end
