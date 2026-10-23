import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Card

/-! The unoriented four-node path has at most two automorphisms.
This finite graph lemma deliberately allows reversal, as needed when
root lengths may be interchanged in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFourRootPathPermutation

def adjacent (i j : Fin 4) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

def PreservesPath (sigma : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j, adjacent (sigma i) (sigma j) ↔ adjacent i j

instance (i j : Fin 4) : Decidable (adjacent i j) := inferInstanceAs
  (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

instance (sigma : Equiv.Perm (Fin 4)) : Decidable (PreservesPath sigma) :=
  inferInstanceAs (Decidable (∀ i j, adjacent (sigma i) (sigma j) ↔ adjacent i j))

private theorem path_permutations : ∀ sigma : Equiv.Perm (Fin 4),
    PreservesPath sigma ↔ sigma = 1 ∨ sigma = Fin.revPerm := by decide

theorem preservesPath_iff (sigma : Equiv.Perm (Fin 4)) :
    PreservesPath sigma ↔ sigma = 1 ∨ sigma = Fin.revPerm := path_permutations sigma

def pathAut : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := PreservesPath
  one_mem' := by intro i j; rfl
  mul_mem' := by intro sigma tau hs ht i j; exact (hs (tau i) (tau j)).trans (ht i j)
  inv_mem' := by
    intro sigma hs i j
    have hh := (hs (sigma⁻¹ i) (sigma⁻¹ j)).symm
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hh

theorem pathAut_card_le_two : Nat.card pathAut ≤ 2 := by
  classical
  let f : pathAut → ↥({1, Fin.revPerm} : Finset (Equiv.Perm (Fin 4))) :=
    fun s => ⟨s.val, by simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (preservesPath_iff s.val).mp s.property⟩
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : ↥({1, Fin.revPerm} : Finset (Equiv.Perm (Fin 4))) => z.val) he
  exact (Nat.card_le_card_of_injective f hinj).trans (by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two)

end SymmetricSubgroupAsymptotics.CFSGFourRootPathPermutation
