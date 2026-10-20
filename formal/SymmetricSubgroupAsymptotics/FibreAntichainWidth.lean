import Mathlib.Order.Antichain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! Equal fibre labels multiply a base antichain width by the number of
fibres. This is the dimension coefficient in the induced leading argument. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

theorem fibre_antichain_card_le
    {A I C : Type} [Fintype C] (s : Finset A) (point : A → I) (fibre : A → C)
    (rel : I → I → Prop) (w : ℕ)
    (hcode : Function.Injective (fun a => (point a,fibre a)))
    (hwidth : ∀ t : Finset I, IsAntichain rel (t : Set I) → t.card≤w)
    (hanti : ∀ a∈s, ∀ b∈s, a≠b → fibre a=fibre b → ¬rel (point a) (point b)) :
    s.card≤Fintype.card C*w := by
  have hfiber (c : C) : (s.filter (fun a => fibre a=c)).card≤w := by
    let t := s.filter (fun a => fibre a=c)
    have hinj : Set.InjOn point (t : Set A) := by
      intro a ha b hb hab
      exact hcode (Prod.ext hab ((Finset.mem_filter.mp ha).2.trans
        (Finset.mem_filter.mp hb).2.symm))
    have himage : IsAntichain rel (t.image point : Set I) := by
      intro x hx y hy hxy hr
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact hanti a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (fun h => hxy (congrArg point h))
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hr
    calc
      t.card=(t.image point).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ w := hwidth _ himage
  have hsum : s.card=∑ c : C, (s.filter (fun a => fibre a=c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    s.card=∑ c : C, (s.filter (fun a => fibre a=c)).card := hsum
    _ ≤ ∑ _c : C, w := Finset.sum_le_sum (fun c _ => hfiber c)
    _ = Fintype.card C*w := by simp [Nat.mul_comm]

end SymmetricSubgroupAsymptotics
