import SymmetricSubgroupAsymptotics.BinarySixDeletedRepresentation
import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge

/-! Symbolic generation of S6 and A6 by the two pairs required by the
original primitive-sixteen rows16/17. Finite checks compare only six-point
permutations in explicit short words, not all elements of either group. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace SixPointAlternatingSymmetricGenerators

open BinarySixDeletedRepresentation

def swap02Word := (alpha * beta16) ^ 3
def swap24Word := alpha ^ 2 * swap02Word * (alpha ^ 2)⁻¹
def swap41Word := alpha ^ 4 * swap02Word * (alpha ^ 4)⁻¹
def swap01Word :=
  (swap02Word * swap24Word) * swap41Word * (swap02Word * swap24Word)⁻¹
def swap35Word := beta16 * (swap01Word * swap24Word)
def swap45Word := alpha * swap35Word * alpha⁻¹
def rotateWord := alpha * swap45Word

theorem swap01Word_eq : swap01Word = Equiv.swap (0 : Fin 6) 1 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem rotateWord_eq : rotateWord = finRotate 6 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem generated_words_mem (H : Subgroup (Equiv.Perm (Fin 6)))
    (ha : alpha ∈ H) (hb : beta16 ∈ H) :
    swap01Word ∈ H ∧ rotateWord ∈ H := by
  have h02 : swap02Word ∈ H := H.pow_mem (H.mul_mem ha hb) 3
  have h24 : swap24Word ∈ H :=
    H.mul_mem (H.mul_mem (H.pow_mem ha 2) h02) (H.inv_mem (H.pow_mem ha 2))
  have h41 : swap41Word ∈ H :=
    H.mul_mem (H.mul_mem (H.pow_mem ha 4) h02) (H.inv_mem (H.pow_mem ha 4))
  have h01 : swap01Word ∈ H := H.mul_mem
    (H.mul_mem (H.mul_mem h02 h24) h41) (H.inv_mem (H.mul_mem h02 h24))
  have h35 : swap35Word ∈ H := H.mul_mem hb (H.mul_mem h01 h24)
  have h45 : swap45Word ∈ H := H.mul_mem (H.mul_mem ha h35) (H.inv_mem ha)
  exact ⟨h01, H.mul_mem ha h45⟩

theorem symmetric_generators :
    Subgroup.closure ({alpha, beta16} : Set (Equiv.Perm (Fin 6))) = ⊤ := by
  let H := Subgroup.closure ({alpha, beta16} : Set (Equiv.Perm (Fin 6)))
  obtain ⟨hs, hr⟩ := generated_words_mem H
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  rw [swap01Word_eq] at hs
  rw [rotateWord_eq] at hr
  have hgen : Subgroup.closure
      ({finRotate 6, Equiv.swap (0 : Fin 6) 1} : Set (Equiv.Perm (Fin 6))) = ⊤ := by
    simpa only [show finRotate 6 (0 : Fin 6) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 6))
        (support_finRotate_of_le (by decide : 2 ≤ 6)) (0 : Fin 6)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact hr
  · exact hs

theorem alpha_even : alpha ∈ alternatingGroup (Fin 6) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  norm_num [alpha, Fin.sign_cycleRange]

theorem beta17_even : beta17 ∈ alternatingGroup (Fin 6) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  rw [beta17, map_mul, map_mul, map_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 6) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 6) ≠ 4),
    Equiv.Perm.sign_swap (by decide : (4 : Fin 6) ≠ 5)]
  norm_num

theorem beta16_inv : beta16⁻¹ = beta16 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have hh := congrArg (fun p : Equiv.Perm (Fin 6) => p 0) h
  change (1 : Fin 6) = 0 at hh
  exact (by decide : (1 : Fin 6) ≠ 0) hh

theorem commutator_word :
    alpha⁻¹ * beta16 * alpha * beta16 = (alpha ^ 3)⁻¹ * beta17⁻¹ * alpha ^ 3 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem alternating_generators :
    Subgroup.closure ({alpha, beta17} : Set (Equiv.Perm (Fin 6))) =
      alternatingGroup (Fin 6) := by
  let H := Subgroup.closure ({alpha, beta17} : Set (Equiv.Perm (Fin 6)))
  have ha : alpha ∈ H := Subgroup.subset_closure (by simp)
  have hb : beta17 ∈ H := Subgroup.subset_closure (by simp)
  have hu : alpha⁻¹ * beta16 * alpha * beta16 ∈ H := by
    rw [commutator_word]
    exact H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem ha 3)) (H.inv_mem hb))
      (H.pow_mem ha 3)
  have hsmall := involutionCommutatorClosure_eq_alternating (by norm_num : 5 ≤ Nat.card (Fin 6))
    alpha beta16 beta16_inv symmetric_generators alpha_even alpha_ne_one
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact alpha_even
    · exact beta17_even
  · rw [← hsmall]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hu

end SixPointAlternatingSymmetricGenerators
end SymmetricSubgroupAsymptotics

end
