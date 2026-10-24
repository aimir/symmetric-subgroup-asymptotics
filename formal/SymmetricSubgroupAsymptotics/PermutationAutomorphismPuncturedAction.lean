import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Coset.Card

/-! The actual faithful action of an automorphism complement on its
original nonidentity translation elements. No linear coordinates are
needed, and the point removed is the literal group identity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PermutationAutomorphismPuncturedAction

abbrev Punctured (V : Type) [Group V] := {v:V // v≠1}

def puncturedHom {V H : Type} [Group V] [Group H] (φ : H→*MulAut V) :
    H→*Equiv.Perm (Punctured V) where
  toFun h := (φ h).toEquiv.subtypeEquiv (fun v=>by
    constructor
    · intro hv he
      exact hv ((φ h).injective (he.trans (map_one (φ h)).symm))
    · intro hv he
      apply hv
      change φ h v=1
      rw [he]
      exact map_one (φ h))
  map_one' := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    change φ 1 v.val=v.val
    rw [map_one]
    rfl
  map_mul' h k := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    change φ (h*k) v.val=φ h (φ k v.val)
    rw [map_mul]
    rfl

theorem puncturedHom_injective {V H : Type} [Group V] [Group H] (φ : H→*MulAut V)
    (hφ : Function.Injective φ) : Function.Injective (puncturedHom φ) := by
  intro h k hh
  apply hφ
  apply MulEquiv.ext
  intro v
  by_cases hv:v=1
  · subst v; simp only [map_one]
  · exact congrArg Subtype.val (Equiv.congr_fun hh (⟨v,hv⟩:Punctured V))

theorem punctured_card (V : Type) [Group V] [Finite V] :
    Nat.card (Punctured V)=Nat.card V-1 := by
  letI : Fintype V := Fintype.ofFinite V
  change Nat.card {v:V // v≠1}=Nat.card V-1
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype_eq] using
    Fintype.card_subtype_compl (fun v:V=>v=1)

theorem card_dvd_punctured_factorial {V H : Type} [Group V] [Finite V] [Group H]
    (φ : H→*MulAut V) (hφ : Function.Injective φ) :
    Nat.card H∣(Nat.card V-1).factorial := by
  have h := Subgroup.card_dvd_of_injective (puncturedHom φ) (puncturedHom_injective φ hφ)
  simpa only [Nat.card_perm,punctured_card] using h

end SymmetricSubgroupAsymptotics.PermutationAutomorphismPuncturedAction
