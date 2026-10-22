import SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicDoubleSwap

/-! The length-five base of the same rotation/double-swap construction.
The third translate shares one transposition with the original double
swap, so that factor cancels and leaves an adjacent three-cycle. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingFiveCycleGeneration
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap
open CFSGPermutationCrossSwapWords

theorem five_conjugate_doubleSwap :
    rotation 1 ^ 3 * adjacentDoubleSwap 1 * (rotation 1 ^ 3)⁻¹ =
      doubleSwap (3 : Cycle 1) 4 0 1 := by
  rw [show adjacentDoubleSwap 1 = doubleSwap (0 : Cycle 1) 1 2 3 from rfl,
    CFSGAlternatingDoubleSwapGeneration.conjugate_doubleSwap]
  have h0 : (rotation 1 ^ 3) (0 : Cycle 1) = 3 := by
    rw [rotation_pow_apply]; decide
  have h1 : (rotation 1 ^ 3) (1 : Cycle 1) = 4 := by
    rw [rotation_pow_apply]; decide
  have h2 : (rotation 1 ^ 3) (2 : Cycle 1) = 0 := by
    rw [rotation_pow_apply]; decide
  have h3 : (rotation 1 ^ 3) (3 : Cycle 1) = 1 := by
    rw [rotation_pow_apply]; decide
  rw [h0, h1, h2, h3]

theorem shared_swap_word (a b c d e : Cycle 1) :
    doubleSwap d e a b * doubleSwap a b c d = Equiv.swap d e * Equiv.swap c d := by
  dsimp only [doubleSwap]
  calc
    (Equiv.swap d e * Equiv.swap a b) * (Equiv.swap a b * Equiv.swap c d) =
        Equiv.swap d e * (Equiv.swap a b * Equiv.swap a b) * Equiv.swap c d := by group
    _ = _ := by rw [Equiv.swap_mul_self, mul_one]

theorem alternating_le_of_five_rotation_doubleSwap
    (G : Subgroup (Equiv.Perm (Cycle 1)))
    (hg : rotation 1 ∈ G) (ha : adjacentDoubleSwap 1 ∈ G) :
    alternatingGroup (Cycle 1) ≤ G := by
  have hb : doubleSwap (3 : Cycle 1) 4 0 1 ∈ G := by
    have h := G.mul_mem (G.mul_mem (G.pow_mem hg 3) ha) (G.inv_mem (G.pow_mem hg 3))
    rwa [five_conjugate_doubleSwap] at h
  have ht : Equiv.swap (2 : Cycle 1) 3 * Equiv.swap 3 4 ∈ G := by
    have h := G.inv_mem (G.mul_mem hb ha)
    rw [show adjacentDoubleSwap 1 = doubleSwap (0 : Cycle 1) 1 2 3 from rfl,
      shared_swap_word, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv] at h
    exact h
  have hc : Subgroup.closure
      ({rotation 1, Equiv.swap (2 : Cycle 1) 3 * Equiv.swap 3 4} :
        Set (Equiv.Perm (Cycle 1))) = alternatingGroup (Cycle 1) := by
    apply evenPairClosure_eq_alternating (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
      (rotation 1) (Equiv.swap (3 : Cycle 1) 4) _ (Equiv.swap_inv _ _)
    · simpa only [show rotation 1 (3 : Cycle 1) = 4 by decide] using
        Equiv.Perm.closure_cycle_adjacent_swap (rotation_isCycle 1 (by decide))
          (rotation_support 1 (by decide)) (3 : Cycle 1)
    · exact Equiv.Perm.mem_alternatingGroup.mpr (rotation_even 1)
    · exact (rotation_isCycle 1 (by decide)).ne_one
    · exact Or.inl (cycle_adjacent_commutator (rotation 1) (2 : Cycle 1) 3 4
        (by decide) (by decide))
  rw [← hc]
  exact (Subgroup.closure_le _).mpr (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg
    · exact ht)

end SymmetricSubgroupAsymptotics.CFSGAlternatingFiveCycleGeneration
