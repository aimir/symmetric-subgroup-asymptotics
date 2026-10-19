import SymmetricSubgroupAsymptotics.MarkedC4ActiveFiberPermutation

/-! Every orbit in the constructed compressed action stays in its
original fiber. Its size bound is proved by an explicit injection. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActiveFiberOrbitBounds
open ActiveFiberPermutation
variable {I G : Type} [Group G] (F : I → Type) [∀ i,MulAction G (F i)]

theorem orbit_card_le (i : I) (x : F i) (hi : Nat.card (F i)≠1) [Finite (F i)] :
    Nat.card (MulAction.orbit G (⟨i,⟨x,hi⟩⟩ : Support F))≤Nat.card (F i) := by
  let z : Support F := ⟨i,⟨x,hi⟩⟩
  let f : MulAction.orbit G z → F i := fun y => (Classical.choose y.property) • x
  have hf (y : MulAction.orbit G z) :
      (y : Support F)=⟨i,⟨f y,hi⟩⟩ := (Classical.choose_spec y.property).symm
  apply Nat.card_le_card_of_injective f
  intro y w h
  apply Subtype.ext
  calc
    (y : Support F) = ⟨i,⟨f y,hi⟩⟩ := hf y
    _ = ⟨i,⟨f w,hi⟩⟩ := by rw [h]
    _ = w := (hf w).symm

theorem cutoff [∀ i,Finite (F i)] {C : ℕ} (hC : ∀ i,Nat.card (F i)<C) :
    ∀ z : Support F, Nat.card (MulAction.orbit G z)<C := by
  rintro ⟨i,x,hi⟩
  exact (orbit_card_le F i x hi).trans_lt (hC i)
end SymmetricSubgroupAsymptotics.MarkedC4.ActiveFiberOrbitBounds
