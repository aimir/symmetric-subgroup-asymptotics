import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-! Telescoping cardinal upper bounds for a finite integer filtration.
Two finite degree sets account for each layer's exponent. The end bound
needs no surjectivity or exact fixed-point sequence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteWeightedTailCardinality

private def degreePartition {X:Type*} (d:X→ℤ) (h:ℤ) :
    {x:X // h≤d x}≃({x:X // d x=h}⊕{x:X // h+1≤d x}) where
  toFun x:=if he:d x.val=h then Sum.inl ⟨x.val,he⟩ else Sum.inr ⟨x.val,by have := x.property;omega⟩
  invFun x:=match x with
    | Sum.inl y=>⟨y.val,by have := y.property;omega⟩
    | Sum.inr y=>⟨y.val,by have := y.property;omega⟩
  left_inv x:=by
    dsimp only
    split_ifs <;> rfl
  right_inv x:=by
    cases x with
    | inl x=>simp only [dif_pos x.property]
    | inr x=>
      have hn : d x.val≠h := by have := x.property;omega
      simp only [dif_neg hn]

theorem degree_tail_card (X:Type*) [Finite X] (d:X→ℤ) (h:ℤ) :
    Nat.card {x:X // h≤d x}=Nat.card {x:X // d x=h}+Nat.card {x:X // h+1≤d x} :=
  (Nat.card_congr (degreePartition d h)).trans Nat.card_sum

theorem square_bound_of_degree_steps (X Y:Type*) [Finite X] [Finite Y]
    (d:X→ℤ) (e:Y→ℤ) (hd:∀x,1≤d x) (he:∀y,1≤e y)
    (q B:ℕ) (hq:1≤q) (a:ℤ→ℕ) (hend:a ((B:ℤ)+1)=1)
    (hstep:∀h:ℤ,0<h→a h^2≤q^(Nat.card {x:X // d x=h}+Nat.card {y:Y // e y=h})*a (h+1)^2) :
    a 1^2≤q^(Nat.card X+Nat.card Y) := by
  have H : ∀n:ℕ,∀h:ℤ,0<h→h+(n:ℤ)=(B:ℤ)+1→
      a h^2≤q^(Nat.card {x:X // h≤d x}+Nat.card {y:Y // h≤e y}) := by
    intro n
    induction n with
    | zero=>
      intro h hh hn
      have hh' : h=(B:ℤ)+1 := by omega
      rw [hh',hend,one_pow]
      exact Nat.one_le_pow _ _ (by omega)
    | succ n ih=>
      intro h hh hn
      have hb := ih (h+1) (by omega) (by push_cast at hn ⊢;omega)
      have hx := degree_tail_card X d h
      have hy := degree_tail_card Y e h
      calc
        a h^2≤q^(Nat.card {x:X // d x=h}+Nat.card {y:Y // e y=h})*a (h+1)^2 := hstep h hh
        _≤q^(Nat.card {x:X // d x=h}+Nat.card {y:Y // e y=h})*
          q^(Nat.card {x:X // h+1≤d x}+Nat.card {y:Y // h+1≤e y}) := Nat.mul_le_mul_left _ hb
        _=q^(Nat.card {x:X // h≤d x}+Nat.card {y:Y // h≤e y}) := by
          rw [←pow_add]
          congr 1
          omega
  have hx : Nat.card {x:X // (1:ℤ)≤d x}=Nat.card X := Nat.card_congr
    (Equiv.ofBijective (fun x:{x:X // (1:ℤ)≤d x}=>x.val)
      ⟨Subtype.val_injective,fun x=>⟨⟨x,hd x⟩,rfl⟩⟩)
  have hy : Nat.card {y:Y // (1:ℤ)≤e y}=Nat.card Y := Nat.card_congr
    (Equiv.ofBijective (fun y:{y:Y // (1:ℤ)≤e y}=>y.val)
      ⟨Subtype.val_injective,fun y=>⟨⟨y,he y⟩,rfl⟩⟩)
  simpa only [hx,hy] using H B 1 (by omega) (by omega)

end SymmetricSubgroupAsymptotics.FiniteWeightedTailCardinality
