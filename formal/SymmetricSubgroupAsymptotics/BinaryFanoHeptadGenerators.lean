import SymmetricSubgroupAsymptotics.BinaryFanoHeptadData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightNaturalTops
import Mathlib.Logic.Equiv.Fin.Basic

/-! Symbolic generation of the alternating sources used by the heptad
action. All fixed permutation equalities concern only seven or eight
labels; no alternating group is enumerated. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFanoHeptadGenerators

open BinaryFanoHeptadData
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Source7 := alternatingGroup (Fin 7)
abbrev Source8 := alternatingGroup (Fin 8)

def beta7 : Equiv.Perm (Fin 7) := finRotate 7
def alpha7 : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem beta7_even : beta7 ∈ alternatingGroup (Fin 7) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  decide +kernel

theorem alpha7_even : alpha7 ∈ alternatingGroup (Fin 7) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  decide +kernel

theorem beta_even : beta ∈ alternatingGroup (Fin 8) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  decide +kernel

theorem alpha_even : alpha ∈ alternatingGroup (Fin 8) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  decide +kernel

theorem gamma_even : gamma ∈ alternatingGroup (Fin 8) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  decide +kernel

theorem generators7 :
    Subgroup.closure ({beta7, alpha7} : Set (Equiv.Perm (Fin 7))) =
      alternatingGroup (Fin 7) := by
  apply evenPairClosure_eq_alternating (by norm_num)
    beta7 (Equiv.swap (1 : Fin 7) 2) alpha7 (Equiv.swap_inv _ _)
  · simpa only [beta7, show finRotate 7 (1 : Fin 7) = 2 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide))
        (support_finRotate_of_le (by decide)) (1 : Fin 7)
  · exact beta7_even
  · decide +kernel
  · left
    decide +kernel

theorem generators8 :
    Subgroup.closure ({beta, gamma} : Set (Equiv.Perm (Fin 8))) =
      alternatingGroup (Fin 8) := by
  let H := Subgroup.closure ({beta, gamma} : Set (Equiv.Perm (Fin 8)))
  have hb : beta ∈ H := Subgroup.subset_closure (by simp)
  have hc : gamma ∈ H := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp
    · rw [hp]; exact beta_even
    · rw [hp]; exact gamma_even
  · rw [← DegreeTwoPairedEightSharedTops.top23_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change DegreeTwoPairedEightSharedTops.top23Generators 0 ∈ H
      have he : DegreeTwoPairedEightSharedTops.top23Generators 0 = beta := by
        apply Equiv.ext; intro x; revert x; decide +kernel
      rw [he]
      exact hb
    · change DegreeTwoPairedEightSharedTops.top23Generators 1 ∈ H
      have he : DegreeTwoPairedEightSharedTops.top23Generators 1 =
          (beta ^ 2)⁻¹ * gamma * beta ^ 2 := by
        apply Equiv.ext; intro x; revert x; decide +kernel
      rw [he]
      exact H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem hb 2)) hc) (H.pow_mem hb 2)

def b7 : Source7 := ⟨beta7, beta7_even⟩
def a7 : Source7 := ⟨alpha7, alpha7_even⟩
def b8 : Source8 := ⟨beta, beta_even⟩
def a8 : Source8 := ⟨alpha, alpha_even⟩
def c8 : Source8 := ⟨gamma, gamma_even⟩

theorem closure_pair_subtype_top {G : Type*} [Group G] (A : Subgroup G)
    (a b : A) (h : Subgroup.closure ({(a : G), (b : G)} : Set G) = A) :
    Subgroup.closure ({a, b} : Set A) = ⊤ := by
  apply Subgroup.map_injective A.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa only [Set.image_insert_eq, Set.image_singleton] using h

theorem source7_generators : Subgroup.closure ({b7, a7} : Set Source7) = ⊤ :=
  closure_pair_subtype_top _ _ _ generators7

theorem source8_generators : Subgroup.closure ({b8, c8} : Set Source8) = ⊤ :=
  closure_pair_subtype_top _ _ _ generators8

/-- Extend a seven-label permutation by fixing the eighth label. -/
def embed7 : Equiv.Perm (Fin 7) →* Equiv.Perm (Fin 8) :=
  Equiv.Perm.extendDomainHom (Fin.castLEquiv (by decide : 7 ≤ 8))

theorem embed7_beta7 : embed7 beta7 = beta := by
  apply Equiv.ext; intro x; revert x; decide +kernel

theorem embed7_alpha7 : embed7 alpha7 = alpha := by
  apply Equiv.ext; intro x; revert x; decide +kernel

def include7 : Source7 →* Source8 :=
  (embed7.comp (alternatingGroup (Fin 7)).subtype).codRestrict _ (by
    intro g
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign ((g : Equiv.Perm (Fin 7)).extendDomain
      (Fin.castLEquiv (by decide : 7 ≤ 8))) = 1
    rw [Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.mp g.2)

theorem include7_b7 : include7 b7 = b8 := by
  apply Subtype.ext
  exact embed7_beta7

theorem include7_a7 : include7 a7 = a8 := by
  apply Subtype.ext
  exact embed7_alpha7

end BinaryFanoHeptadGenerators
end SymmetricSubgroupAsymptotics

end
