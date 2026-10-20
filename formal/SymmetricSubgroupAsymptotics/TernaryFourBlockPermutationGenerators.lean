import SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage
import Mathlib.GroupTheory.Perm.Closure

/-! Symbolic generation of the actual A4/S4 block complements. The only
finite word certificate concerns three distinct labels among four, not
an enumeration of the generated group or its subgroups. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

def a : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
def b : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
def c : Equiv.Perm (Fin 4) := finRotate 4
def s : Equiv.Perm (Fin 4) := Equiv.swap 2 3

theorem a_even : a ∈ alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign a = 1
  decide +kernel
theorem b_even : b ∈ alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign b = 1
  decide +kernel

private def tripleWords : Fin 8 → Equiv.Perm (Fin 4) :=
  ![a,a⁻¹,b,b⁻¹,b*a*b⁻¹,b*a⁻¹*b⁻¹,b^2*a*(b^2)⁻¹,b^2*a⁻¹*(b^2)⁻¹]

private theorem triple_word : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    ∃ w : Fin 8, Equiv.swap i j * Equiv.swap j k = tripleWords w := by
  decide +kernel

theorem alternating_generated :
    Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin 4))) = alternatingGroup (Fin 4) := by
  let H := Subgroup.closure ({a,b} : Set (Equiv.Perm (Fin 4)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  have hw (w : Fin 8) : tripleWords w ∈ H := by
    fin_cases w
    · exact ha
    · exact H.inv_mem ha
    · exact hb
    · exact H.inv_mem hb
    · exact H.mul_mem (H.mul_mem hb ha) (H.inv_mem hb)
    · exact H.mul_mem (H.mul_mem hb (H.inv_mem ha)) (H.inv_mem hb)
    · exact H.mul_mem (H.mul_mem (H.pow_mem hb 2) ha) (H.inv_mem (H.pow_mem hb 2))
    · exact H.mul_mem (H.mul_mem (H.pow_mem hb 2) (H.inv_mem ha))
        (H.inv_mem (H.pow_mem hb 2))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact a_even
    · exact b_even
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    have hcycle : g.IsThreeCycle := hg
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by rw [hcycle.card_support]; decide)
    have hn : i ≠ g i ∧ i ≠ g (g i) ∧ g i ≠ g (g i) := by
      simpa [List.nodup_cons,not_or,and_assoc] using
        (hcycle.nodup_iff_mem_support.mpr hi)
    obtain ⟨hij,hik,hjk⟩ := hn
    obtain ⟨w,hwg⟩ := triple_word i (g i) (g (g i)) hij hik hjk
    rw [hcycle.eq_swap_mul_swap_iff_mem_support.mpr hi,hwg]
    exact hw w

theorem symmetric_generated :
    Subgroup.closure ({c,s} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
  simpa only [c,s,show finRotate 4 (2 : Fin 4) = 3 from rfl] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide : 2 ≤ 4))
      (support_finRotate_of_le (by decide : 2 ≤ 4)) (2 : Fin 4)

end SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

end
