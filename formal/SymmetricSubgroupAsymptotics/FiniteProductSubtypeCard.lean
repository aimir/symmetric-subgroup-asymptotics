import Mathlib.Data.Fintype.BigOperators

/-! Count an actual product predicate by its small literal fibres. The
equivalence is structural; individual finite fibre counts can then be
checked separately without evaluating one large subtype enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics
open scoped BigOperators

theorem product_subtype_card_eq_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B → Prop) [DecidablePred p] :
    Fintype.card {x // p x} = ∑ b : B, Fintype.card {a : A // p (a,b)} := by
  let e : {x // p x} ≃ (Σ b : B, {a : A // p (a,b)}) := {
    toFun x := ⟨x.val.2, ⟨x.val.1, x.property⟩⟩
    invFun x := ⟨(x.2.val,x.1),x.2.property⟩
    left_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl
    right_inv := by rintro ⟨b,⟨a,h⟩⟩; rfl }
  exact (Fintype.card_congr e).trans Fintype.card_sigma

end SymmetricSubgroupAsymptotics
