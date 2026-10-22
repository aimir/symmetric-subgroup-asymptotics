import SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicReflection
import SymmetricSubgroupAsymptotics.CFSGAlternatingSumSupport
import Mathlib.Tactic.FinCases

/-! Literal orbit arguments for a long cycle with at most three outsiders.
All cycle points are in one orbit. Two explicit cross images absorb two
outsiders; if only one point remains, any group element moving it absorbs it
as well. This is an action proof, not a subgroup census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSumTransitivity
open CFSGAlternatingCyclicReflection CFSGAlternatingSumSupport

theorem pretransitive_of_reaches_except_one
    {X : Type*} [DecidableEq X] (K : Subgroup (Equiv.Perm X)) (b z : X)
    (hreach : ∀ x, x ≠ z → ∃ h : K, (h : Equiv.Perm X) b = x)
    (hmove : ∃ h : K, (h : Equiv.Perm X) z ≠ z) : MulAction.IsPretransitive K X := by
  apply (MulAction.isPretransitive_iff_base b).mpr
  intro x
  by_cases hx : x = z
  · subst x
    obtain ⟨h, hh⟩ := hmove
    obtain ⟨a, ha⟩ := hreach ((h : Equiv.Perm X) z) hh
    refine ⟨h⁻¹ * a, ?_⟩
    change (h.val)⁻¹ (a.val b) = z
    rw [ha]
    exact h.val.symm_apply_apply z
  · exact hreach x hx

theorem reaches_cycle (k r : ℕ) (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin r)))
    (hg : extensionHom (Cycle k) r (rotation k) ∈ K) (x : Cycle k) :
    ∃ h : K, (h : Equiv.Perm (Cycle k ⊕ Fin r)) (Sum.inl 0) = Sum.inl x := by
  refine ⟨⟨extensionHom (Cycle k) r (rotation k) ^ x.val, K.pow_mem hg x.val⟩, ?_⟩
  change (extensionHom (Cycle k) r (rotation k) ^ x.val) (Sum.inl 0) = _
  rw [← map_pow, extension_apply_left, rotation_pow_apply, zero_add, ZMod.natCast_zmod_val]

theorem reaches_outsider_of_cross_image (k r : ℕ)
    (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin r)))
    (hg : extensionHom (Cycle k) r (rotation k) ∈ K)
    (i : Fin r) (h : K) (x : Cycle k)
    (hcross : (h : Equiv.Perm (Cycle k ⊕ Fin r)) (Sum.inr i) = Sum.inl x) :
    ∃ a : K, (a : Equiv.Perm (Cycle k ⊕ Fin r)) (Sum.inl 0) = Sum.inr i := by
  obtain ⟨a, ha⟩ := reaches_cycle k r K hg x
  refine ⟨h⁻¹ * a, ?_⟩
  change (h.val)⁻¹ (a.val (Sum.inl 0)) = Sum.inr i
  rw [ha, ← hcross]
  exact h.val.symm_apply_apply _

theorem pretransitive_zero (k : ℕ) (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin 0)))
    (hg : extensionHom (Cycle k) 0 (rotation k) ∈ K) :
    MulAction.IsPretransitive K (Cycle k ⊕ Fin 0) := by
  apply (MulAction.isPretransitive_iff_base (Sum.inl (0 : Cycle k))).mpr
  intro x
  cases x with
  | inl x => exact reaches_cycle k 0 K hg x
  | inr i => exact Fin.elim0 i

theorem pretransitive_one (k : ℕ) (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin 1)))
    (hg : extensionHom (Cycle k) 1 (rotation k) ∈ K)
    (hmove : ∃ h : K, (h : Equiv.Perm (Cycle k ⊕ Fin 1)) (Sum.inr 0) ≠ Sum.inr 0) :
    MulAction.IsPretransitive K (Cycle k ⊕ Fin 1) := by
  apply pretransitive_of_reaches_except_one K (Sum.inl 0) (Sum.inr 0) _ hmove
  intro x hx
  cases x with
  | inl x => exact reaches_cycle k 1 K hg x
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      exact False.elim (hx (congrArg Sum.inr hi))

theorem pretransitive_two (k : ℕ) (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin 2)))
    (hg : extensionHom (Cycle k) 2 (rotation k) ∈ K)
    (hcross : ∀ i : Fin 2, ∃ h : K, ∃ x : Cycle k,
      (h : Equiv.Perm (Cycle k ⊕ Fin 2)) (Sum.inr i) = Sum.inl x) :
    MulAction.IsPretransitive K (Cycle k ⊕ Fin 2) := by
  apply (MulAction.isPretransitive_iff_base (Sum.inl (0 : Cycle k))).mpr
  intro x
  cases x with
  | inl x => exact reaches_cycle k 2 K hg x
  | inr i =>
      obtain ⟨h, x, hh⟩ := hcross i
      exact reaches_outsider_of_cross_image k 2 K hg i h x hh

theorem pretransitive_three (k : ℕ) (K : Subgroup (Equiv.Perm (Cycle k ⊕ Fin 3)))
    (hg : extensionHom (Cycle k) 3 (rotation k) ∈ K)
    (hcross : ∀ i : Fin 2, ∃ h : K, ∃ x : Cycle k,
      (h : Equiv.Perm (Cycle k ⊕ Fin 3)) (Sum.inr i.castSucc) = Sum.inl x)
    (hmove : ∃ h : K, (h : Equiv.Perm (Cycle k ⊕ Fin 3)) (Sum.inr 2) ≠ Sum.inr 2) :
    MulAction.IsPretransitive K (Cycle k ⊕ Fin 3) := by
  apply pretransitive_of_reaches_except_one K (Sum.inl 0) (Sum.inr 2) _ hmove
  intro x hx
  cases x with
  | inl x => exact reaches_cycle k 3 K hg x
  | inr i =>
      have hi : i ≠ 2 := fun h => hx (congrArg Sum.inr h)
      have hlt : i.val < 2 := by
        have hn : i.val ≠ 2 := fun h => hi (Fin.ext h)
        omega
      let j : Fin 2 := ⟨i.val, hlt⟩
      obtain ⟨h, x, hh⟩ := hcross j
      have hji : j.castSucc = i := Fin.ext rfl
      rw [hji] at hh
      exact reaches_outsider_of_cross_image k 3 K hg i h x hh

end SymmetricSubgroupAsymptotics.CFSGAlternatingSumTransitivity
