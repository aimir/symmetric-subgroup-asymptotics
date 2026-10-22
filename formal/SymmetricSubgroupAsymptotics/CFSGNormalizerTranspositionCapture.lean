import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowCanonicalMatching
import SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionClasses
import Mathlib.Data.Set.Card

/-! A subgroup with transposition classes of size at most two cannot add
any transposition to a contained symmetric Sylow two-subgroup. Canonical
Sylow partners and the at-most-one unmatched point prove this literally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionCapture
open Equiv CFSGNormalizerTranspositionClasses CFSGSymmetricSylowCanonicalMatching

theorem partner_unique_of_small_classes {X : Type*} [Finite X] [DecidableEq X]
    (N : Subgroup (Perm X)) (hsize : ∀ x, (pointClass N x).ncard ≤ 2)
    {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxyN : Equiv.swap x y ∈ N) (hxzN : Equiv.swap x z ∈ N) : y = z := by
  by_contra hyz
  have hlarge : 2 < (pointClass N x).ncard := by
    rw [Set.two_lt_ncard_iff]
    exact ⟨x, y, z, related_refl N x, hxyN, hxzN, hxy, hxz, hyz⟩
  have hsmall := hsize x
  omega

theorem swap_mem_sylow_of_small_classes {X : Type*} [Finite X] [DecidableEq X]
    (N : Subgroup (Perm X)) (hsize : ∀ x, (pointClass N x).ncard ≤ 2)
    (Q : Sylow 2 (Perm X)) (hQN : (Q : Subgroup (Perm X)) ≤ N)
    (x y : X) (hxyN : Equiv.swap x y ∈ N) : Equiv.swap x y ∈ Q := by
  by_cases hxy : x = y
  · subst y
    rw [Equiv.swap_self]
    exact Q.one_mem
  by_cases hx : HasPartner Q x
  · obtain ⟨z, hzx, hxzQ⟩ := hx
    have he : y = z := partner_unique_of_small_classes N hsize hxy (Ne.symm hzx) hxyN (hQN hxzQ)
    simpa only [he] using hxzQ
  by_cases hy : HasPartner Q y
  · obtain ⟨z, hzy, hyzQ⟩ := hy
    have hyxN : Equiv.swap y x ∈ N := by simpa only [Equiv.swap_comm] using hxyN
    have he : x = z := partner_unique_of_small_classes N hsize (Ne.symm hxy) (Ne.symm hzy)
      hyxN (hQN hyzQ)
    have h : Equiv.swap y x ∈ Q := by simpa only [← he] using hyzQ
    simpa only [Equiv.swap_comm] using h
  exact False.elim (hxy (unmatched_subsingleton Q hx hy))

end SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionCapture
