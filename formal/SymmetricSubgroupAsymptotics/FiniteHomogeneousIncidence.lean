import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite double counting with equal right fibres. No transitivity of
an automorphism action on an ambient permutation domain is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHomogeneousIncidence

def swapIncidence {Y X : Type*} (R : Y → X → Prop) :
    ((y : Y) × {x : X // R y x}) ≃ ((x : X) × {y : Y // R y x}) where
  toFun z := ⟨z.2.val,⟨z.1,z.2.property⟩⟩
  invFun z := ⟨z.2.val,⟨z.1,z.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lower_card_mul_le {Y X : Type*} [Finite Y] [Fintype X]
    (R : Y → X → Prop) (x₀ : X) (d : ℕ)
    (hlower : ∀ y : Y, d ≤ Nat.card {x : X // R y x})
    (hequal : ∀ x : X, Nat.card {y : Y // R y x} =
      Nat.card {y : Y // R y x₀}) :
    d * Nat.card Y ≤ Nat.card X * Nat.card {y : Y // R y x₀} := by
  letI : Fintype Y := Fintype.ofFinite _
  have hs : (∑ y : Y, Nat.card {x : X // R y x}) =
      ∑ x : X, Nat.card {y : Y // R y x} := by
    calc
      _ = Nat.card ((y : Y) × {x : X // R y x}) := Nat.card_sigma.symm
      _ = Nat.card ((x : X) × {y : Y // R y x}) := Nat.card_congr (swapIncidence R)
      _ = _ := Nat.card_sigma
  calc
    d * Nat.card Y = ∑ _y : Y, d := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card,Nat.cast_id,Nat.mul_comm]
    _ ≤ ∑ y : Y, Nat.card {x : X // R y x} :=
      Finset.sum_le_sum (fun y _ => hlower y)
    _ = ∑ x : X, Nat.card {y : Y // R y x} := hs
    _ = Nat.card X * Nat.card {y : Y // R y x₀} := by
      simp only [hequal,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card,Nat.cast_id]

theorem card_eq_mul_fibre {Y X : Type*} [Finite Y] [Fintype X]
    (f : Y → X) (x₀ : X)
    (hequal : ∀ x : X, Nat.card {y : Y // f y = x} =
      Nat.card {y : Y // f y = x₀}) :
    Nat.card Y = Nat.card X * Nat.card {y : Y // f y = x₀} := by
  calc
    Nat.card Y = Nat.card ((x : X) × {y : Y // f y = x}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ x : X, Nat.card {y : Y // f y = x} := Nat.card_sigma
    _ = _ := by
      simp only [hequal,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card,Nat.cast_id]

end SymmetricSubgroupAsymptotics.FiniteHomogeneousIncidence
