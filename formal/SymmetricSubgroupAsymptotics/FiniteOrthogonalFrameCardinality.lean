import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Four-coordinate frame counting by bounded successive fibres.
The relation need not be classified or supplied as a permutation group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteOrthogonalFrameCardinality

private theorem card_sigma_le {I:Type*} [Finite I] (C:I→Type*) [∀i,Finite (C i)]
    (n:ℕ) (h:∀i,Nat.card (C i)≤n) : Nat.card (Σi,C i)≤Nat.card I*n := by
  letI : Fintype I := Fintype.ofFinite I
  rw [Nat.card_sigma]
  calc
    (∑i: I,Nat.card (C i))≤∑_i:I,n := Finset.sum_le_sum (fun i _=>h i)
    _=Nat.card I*n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]

def Frames {I:Type*} (R:I→I→Prop) :=
  Σx:I,Σy:{y:I // R x y},Σz:{z:I // R x z∧R y.val z},
    {w:I // R x w∧R y.val w∧R z.val w}

theorem card_frames_le {I:Type*} [Finite I] (R:I→I→Prop)
    (a b c d:ℕ) (hI:Nat.card I≤a)
    (h1:∀x:I,Nat.card {y:I // R x y}≤b)
    (h2:∀(x:I)(y:{y:I // R x y}),Nat.card {z:I // R x z∧R y.val z}≤c)
    (h3:∀(x:I)(y:{y:I // R x y})(z:{z:I // R x z∧R y.val z}),
      Nat.card {w:I // R x w∧R y.val w∧R z.val w}≤d) :
    Nat.card (Frames R)≤a*(b*(c*d)) := by
  letI : Fintype I := Fintype.ofFinite I
  change Nat.card (Σx:I,Σy:{y:I // R x y},Σz:{z:I // R x z∧R y.val z},
    {w:I // R x w∧R y.val w∧R z.val w})≤a*(b*(c*d))
  apply (card_sigma_le _ (b*(c*d)) ?_).trans (Nat.mul_le_mul_right _ hI)
  intro x
  apply (card_sigma_le _ (c*d) ?_).trans (Nat.mul_le_mul_right _ (h1 x))
  intro y
  exact (card_sigma_le _ d (fun z=>h3 x y z)).trans (Nat.mul_le_mul_right _ (h2 x y))

theorem card_subtype_filter {I:Type*} [DecidableEq I] (s:Finset I)
    (P:I→Prop) [DecidablePred P] : Nat.card {x:s // P x.val}=(s.filter P).card := by
  let e : {x:s // P x.val}≃(s.filter P) := {
    toFun x:=⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,x.property⟩⟩
    invFun x:=⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,(Finset.mem_filter.mp x.property).2⟩
    left_inv _:=rfl
    right_inv _:=rfl }
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e

end SymmetricSubgroupAsymptotics.FiniteOrthogonalFrameCardinality
