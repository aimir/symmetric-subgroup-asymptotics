import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Basic

/-! Independent flips of the pairs of an actual involution form a
two-group. Its centralizer normalizes this flip group. Sylow maximality
therefore puts every pair flip into any symmetric Sylow subgroup that
centralizes the involution. No enumeration or normalizer conclusion is
assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGInvolutionPairFlipGroup
open Equiv
variable {X : Type*} (t : Perm X) (ht : Function.Involutive t)

def flips : Subgroup (Perm X) where
  carrier := {g | ∀ x, g x = x ∨ g x = t x}
  one_mem' x := Or.inl rfl
  mul_mem' := by
    intro f g hf hg x
    change f (g x) = x ∨ f (g x) = t x
    rcases hg x with h | h
    · rw [h]
      exact hf x
    · rw [h]
      rcases hf (t x) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans (ht x))
  inv_mem' := by
    intro g hg x
    rcases hg (g.symm x) with h | h
    · left
      exact (g.apply_symm_apply x).symm.trans h |>.symm
    · right
      have he : x = t (g.symm x) := (g.apply_symm_apply x).symm.trans h
      exact ((congrArg t he).trans (ht (g.symm x))).symm

theorem square_eq_one (g : flips t ht) : g ^ 2 = 1 := by
  apply Subtype.ext
  apply Perm.ext
  intro x
  change (g.val) ((g.val) x) = x
  rcases g.property x with h | h
  · rw [h, h]
  · rw [h]
    rcases g.property (t x) with h' | h'
    · have he : x = t x := g.val.injective (h.trans h'.symm)
      exact h'.trans he.symm
    · exact h'.trans (ht x)

theorem isPGroup : IsPGroup 2 (flips t ht) := by
  intro g
  exact ⟨1, by simpa only [pow_one] using square_eq_one t ht g⟩

theorem centralizer_le_normalizer :
    Subgroup.centralizer ({t} : Set (Perm X)) ≤
      Subgroup.normalizer (flips t ht : Set (Perm X)) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro f
  constructor
  · intro hf x
    have hcomm : t * g = g * t := (Subgroup.mem_centralizer_iff.mp hg) t (by simp)
    rcases hf (g.symm x) with h | h
    · left
      change g (f (g.symm x)) = x
      rw [h, g.apply_symm_apply]
    · right
      change g (f (g.symm x)) = t x
      rw [h]
      have he := congrArg (fun u : Perm X => u (g.symm x)) hcomm
      simpa only [Perm.mul_apply, g.apply_symm_apply] using he.symm
  · intro hf x
    have hcomm : t * g = g * t := (Subgroup.mem_centralizer_iff.mp hg) t (by simp)
    rcases hf (g x) with h | h
    · left
      change g (f (g.symm (g x))) = g x at h
      simpa only [g.symm_apply_apply] using g.injective h
    · right
      change g (f (g.symm (g x))) = t (g x) at h
      have he := congrArg (fun u : Perm X => u x) hcomm
      have hh : g (f x) = g (t x) := by
        simpa only [g.symm_apply_apply, Perm.mul_apply] using h.trans he
      exact g.injective hh

theorem swap_mem [DecidableEq X] (x : X) : Equiv.swap x (t x) ∈ flips t ht := by
  intro y
  by_cases hy : y = x
  · subst y
    exact Or.inr (Equiv.swap_apply_left x (t x))
  · by_cases hyt : y = t x
    · subst y
      exact Or.inr ((Equiv.swap_apply_right x (t x)).trans (ht x).symm)
    · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hy hyt)

theorem flips_le_sylow [Finite X] (P : Sylow 2 (Perm X))
    (hP : (P : Subgroup (Perm X)) ≤ Subgroup.centralizer ({t} : Set (Perm X))) :
    flips t ht ≤ P := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := P.isPGroup'.to_sup_of_normal_right' (isPGroup t ht)
    (hP.trans (centralizer_le_normalizer t ht))
  exact le_sup_right.trans (P.is_maximal' hp le_sup_left).le

end SymmetricSubgroupAsymptotics.CFSGInvolutionPairFlipGroup
