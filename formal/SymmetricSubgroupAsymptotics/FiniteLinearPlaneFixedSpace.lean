import SymmetricSubgroupAsymptotics.FiniteLinearPlaneClassBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A nonidentity actual linear automorphism of a nine-element F3 plane
fixes at most three vectors. This follows from its proper fixed subspace;
no matrix census or supplied fixed-point budget occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteLinearPlaneFixedSpace
open FiniteLinearPlaneClassBound

local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
variable {V : Type*} [AddCommGroup V] [Module Scalar V]

theorem finrank_eq_two [Finite V] (hV : Nat.card V = 9) :
    Module.finrank Scalar V = 2 := by
  letI : FiniteDimensional Scalar V := Module.Finite.of_finite
  have hc := Module.natCard_eq_pow_finrank (K := Scalar) (V := V)
  rw [hV, show Nat.card Scalar = 3 from Nat.card_zmod 3] at hc
  apply Nat.pow_right_injective (by decide : 2 ≤ (3 : ℕ))
  simpa only [show (3 : ℕ)^2=9 by decide] using hc.symm

def fixedSubspace (e : V ≃ₗ[Scalar] V) : Submodule Scalar V :=
  (e.toLinearMap-LinearMap.id).ker

theorem fixed_card_le_three [Finite V] (hV : Nat.card V = 9)
    (e : V ≃ₗ[Scalar] V) (he : e ≠ 1) :
    Nat.card {v : V // e v = v} ≤ 3 := by
  letI : FiniteDimensional Scalar V := Module.Finite.of_finite
  have hproper : fixedSubspace e ≠ ⊤ := by
    intro htop
    apply he
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ fixedSubspace e := by rw [htop]; trivial
    have hz : e v-v=0 := hv
    exact sub_eq_zero.mp hz
  have hd := Submodule.finrank_lt hproper
  rw [finrank_eq_two hV] at hd
  let a : {v : V // e v = v} ≃ fixedSubspace e := {
    toFun := fun v => ⟨v.val, by change e v.val-v.val=0; rw [v.property, sub_self]⟩
    invFun := fun v => ⟨v.val, by
      have hz : e v.val-v.val=0 := v.property
      exact sub_eq_zero.mp hz⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card {v : V // e v = v} = Nat.card (fixedSubspace e) := Nat.card_congr a
    _ = 3^Module.finrank Scalar (fixedSubspace e) := by
      rw [Module.natCard_eq_pow_finrank (K := Scalar), Nat.card_zmod]
    _ ≤ 3^1 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 3 := pow_one _

end SymmetricSubgroupAsymptotics.FiniteLinearPlaneFixedSpace
