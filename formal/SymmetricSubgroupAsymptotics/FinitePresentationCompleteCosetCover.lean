import SymmetricSubgroupAsymptotics.FinitePresentationCosetLink
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.List.Induction
import Mathlib.SetTheory.Cardinal.Finite

/-! Complete signed-letter Link certificates give genuine finite coset covers.
Link uses RIGHT cosets. Inversion is retained explicitly when passing to G/H. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FinitePresentationCompleteCosetCover
open FinitePresentationCosetLink
variable {ι G : Type*} [Group G] (H : Subgroup G) (g : ι → G)
  {n : ℕ} (reps : Fin n → Word ι)

structure Certificate where
  initial : ∃ i, Link H g [] (reps i)
  edges : ∀ i (a : ι × Bool), ∃ j, Link H g (reps i ++ [a]) (reps j)

theorem word_covered (C : Certificate H g reps) (w : Word ι) :
    ∃ i, Link H g w (reps i) := by
  induction w using List.reverseRecOn with
  | nil => exact C.initial
  | append_singleton w a ih =>
    obtain ⟨i,hi⟩ := ih
    obtain ⟨j,hj⟩ := C.edges i a
    exact ⟨j, trans (right hi [a]) hj⟩

theorem element_covered (C : Certificate H g reps)
    (hg : Function.Surjective (eval g)) (x : G) :
    ∃ i, x * (eval g (reps i))⁻¹ ∈ H := by
  obtain ⟨w,rfl⟩ := hg x
  exact word_covered H g reps C w

theorem quotient_surjective (C : Certificate H g reps)
    (hg : Function.Surjective (eval g)) :
    Function.Surjective (fun i => (QuotientGroup.mk ((eval g (reps i))⁻¹) : G ⧸ H)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  obtain ⟨i,hi⟩ := element_covered H g reps C hg x⁻¹
  refine ⟨i, QuotientGroup.eq.mpr ?_⟩
  simpa only [inv_inv, mul_inv_rev] using H.inv_mem hi

theorem index_le (C : Certificate H g reps)
    (hg : Function.Surjective (eval g)) : H.index ≤ n := by
  have hs := quotient_surjective H g reps C hg
  have hc := Nat.card_le_card_of_surjective _ hs
  change Nat.card (G ⧸ H) ≤ n
  simpa only [Nat.card_fin] using hc

theorem product_surjective (C : Certificate H g reps)
    (hg : Function.Surjective (eval g)) :
    Function.Surjective (fun p : H × Fin n => (p.1 : G) * eval g (reps p.2)) := by
  intro x
  obtain ⟨i,hi⟩ := element_covered H g reps C hg x
  refine ⟨(⟨x*(eval g (reps i))⁻¹,hi⟩,i),?_⟩
  change (x * (eval g (reps i))⁻¹) * eval g (reps i) = x
  group

theorem finite_and_card_le [Finite H] (C : Certificate H g reps)
    (hg : Function.Surjective (eval g)) : Finite G ∧ Nat.card G ≤ Nat.card H * n := by
  have hs := product_surjective H g reps C hg
  have hfin : Finite G := Finite.of_surjective _ hs
  refine ⟨hfin,?_⟩
  have hc := Nat.card_le_card_of_surjective _ hs
  simpa only [Nat.card_prod,Nat.card_fin] using hc

theorem cyclic_finite_and_card_le (x : G) {m : ℕ} (hm : 0 < m) (hx : x^m=1)
    (C : Certificate (Subgroup.zpowers x) g reps)
    (hg : Function.Surjective (eval g)) : Finite G ∧ Nat.card G ≤ m*n := by
  have hxfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,hx⟩
  letI : Finite (Subgroup.zpowers x) := Finite.of_equiv (Fin (orderOf x)) (finEquivZPowers hxfin)
  have hc : Nat.card (Subgroup.zpowers x) ≤ m := by
    rw [← Nat.card_congr (finEquivZPowers hxfin), Nat.card_fin]
    exact orderOf_le_of_pow_eq_one hm hx
  obtain ⟨hf,hbound⟩ := finite_and_card_le (Subgroup.zpowers x) g reps C hg
  exact ⟨hf,hbound.trans (Nat.mul_le_mul_right n hc)⟩

end SymmetricSubgroupAsymptotics.FinitePresentationCompleteCosetCover
