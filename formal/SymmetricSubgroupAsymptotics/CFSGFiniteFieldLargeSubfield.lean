import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-! A proper subfield has at most the square root of the ambient
field's size. Hence any sufficiently large actual scalar subgroup
generates the whole field. The proof uses a literal two-coordinate
injection and no finite-field classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldLargeSubfield
variable {K : Type*} [Field K] [Finite K]

theorem proper_subfield_card_square_le (F : Subfield K) (hF : F ≠ ⊤) :
    Nat.card F ^ 2 ≤ Nat.card K := by
  obtain ⟨a, ha⟩ : ∃ a : K, a ∉ F := by
    by_contra! hh
    apply hF
    exact top_unique (fun x _ => hh x)
  let f : F × F → K := fun xy => xy.1.val + xy.2.val * a
  have hf : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ he
    change x.val + y.val * a = x'.val + y'.val * a at he
    have hy : y = y' := by
      by_contra hne
      have hd : y.val - y'.val ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
      have hh : a = (x'.val - x.val) / (y.val - y'.val) := by
        apply (eq_div_iff hd).mpr
        linear_combination he
      apply ha
      rw [hh]
      exact F.div_mem (F.sub_mem x'.property x.property) (F.sub_mem y.property y'.property)
    have hx : x = x' := by
      rw [hy] at he
      exact Subtype.ext (add_right_cancel he)
    exact Prod.ext hx hy
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective f hf

theorem subfield_eq_top_of_card_square_lt (F : Subfield K)
    (h : Nat.card K < Nat.card F ^ 2) : F = ⊤ := by
  by_contra hF
  exact h.not_ge (proper_subfield_card_square_le F hF)

theorem closure_unit_subgroup_eq_top (H : Subgroup Kˣ)
    (h : Nat.card K < Nat.card H ^ 2) :
    Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤ := by
  let F := Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ))
  let f : H → F := fun u => ⟨u.val.val, Subfield.subset_closure ⟨u.val, u.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro u v he
    have hv : u.val.val = v.val.val := congrArg (fun x : F => x.val) he
    exact Subtype.ext (Units.ext hv)
  have hc := Nat.card_le_card_of_injective f hf
  exact subfield_eq_top_of_card_square_lt F (h.trans_le (Nat.pow_le_pow_left hc 2))

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldLargeSubfield
