import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Perm.Sign

/-!
# Two-block wreath products

`A ≀ C₂ = (A × A) ⋊ C₂`, with `C₂` exchanging the coordinates, and its
imprimitive action on `X ⊕ X` induced by an action of `A` on `X`.  The
actual two-block orbits `A₄ ≀ C₂` (A4W2) and the three named `S₈` classes
of TF are literal subgroups of such products.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace C2Wreath

open Equiv

/-- The generator of `C₂`. -/
def gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = gen := by
  revert g
  decide

theorem gen_mul_gen : gen * gen = 1 := by decide

theorem gen_inv : gen⁻¹ = gen := by decide

theorem gen_ne_one : gen ≠ 1 := by decide

variable (A : Type*) [Group A]

/-- The coordinate exchange. -/
def swapAut : Multiplicative (ZMod 2) →* MulAut (A × A) where
  toFun g := if g = 1 then 1 else MulEquiv.prodComm
  map_one' := if_pos rfl
  map_mul' g h := by
    rcases cases g with rfl | rfl <;> rcases cases h with rfl | rfl
    · simp
    · simp [gen_ne_one]
    · simp [gen_ne_one]
    · rw [gen_mul_gen, if_pos rfl, if_neg gen_ne_one]
      ext ⟨a, b⟩ <;> rfl

theorem swapAut_one (n : A × A) : swapAut A 1 n = n := by
  simp [swapAut]

theorem swapAut_gen (n : A × A) : swapAut A gen n = (n.2, n.1) := by
  simp [swapAut, gen_ne_one]
  rfl

/-- The two-block wreath product. -/
abbrev W := (A × A) ⋊[swapAut A] Multiplicative (ZMod 2)

variable {A}

theorem mul_left' (x y : W A) :
    (x * y).left = x.left * swapAut A x.right y.left := rfl

/-- The block exchange on `X ⊕ X`. -/
def blockSwap (X : Type*) : Multiplicative (ZMod 2) →* Perm (X ⊕ X) where
  toFun g := if g = 1 then 1 else Equiv.sumComm X X
  map_one' := if_pos rfl
  map_mul' g h := by
    rcases cases g with rfl | rfl <;> rcases cases h with rfl | rfl
    · simp
    · simp [gen_ne_one]
    · simp [gen_ne_one]
    · rw [gen_mul_gen, if_pos rfl, if_neg gen_ne_one]
      ext x
      rcases x with x | x <;> rfl

/-- The imprimitive action of `A ≀ C₂` on `X ⊕ X`. -/
def action {X : Type*} (ρ : A →* Perm X) : W A →* Perm (X ⊕ X) :=
  SemidirectProduct.lift
    ((Perm.sumCongrHom X X).comp (ρ.prodMap ρ))
    (blockSwap X)
    (by
      intro g
      rcases cases g with rfl | rfl
      · ext ⟨a, b⟩ x
        simp [blockSwap]
      · ext ⟨a, b⟩ x
        rcases x with x | x <;>
          simp [swapAut_gen, blockSwap, gen_ne_one, MulAut.conj_apply])

theorem action_inl {X : Type*} (ρ : A →* Perm X) (n : A × A) :
    action ρ (SemidirectProduct.inl n) = Perm.sumCongr (ρ n.1) (ρ n.2) := by
  simp [action]

theorem action_inr_gen {X : Type*} (ρ : A →* Perm X) :
    action ρ (SemidirectProduct.inr gen) = Equiv.sumComm X X := by
  simp [action, blockSwap, gen_ne_one]

theorem action_injective {X : Type*} [Nonempty X] (ρ : A →* Perm X)
    (hρ : Function.Injective ρ) :
    Function.Injective (action ρ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [← SemidirectProduct.inl_left_mul_inr_right x] at hx ⊢
  rcases cases x.right with h | h
  · rw [h, map_one, mul_one] at hx ⊢
    rw [action_inl] at hx
    have h1 : ρ x.left.1 = 1 := by
      ext y
      have := congrArg (fun σ : Perm (X ⊕ X) => σ (Sum.inl y)) hx
      simpa using this
    have h2 : ρ x.left.2 = 1 := by
      ext y
      have := congrArg (fun σ : Perm (X ⊕ X) => σ (Sum.inr y)) hx
      simpa using this
    have e1 := hρ (h1.trans (map_one ρ).symm)
    have e2 := hρ (h2.trans (map_one ρ).symm)
    have : x.left = 1 := Prod.ext e1 e2
    rw [this, map_one]
  · exfalso
    rw [h, map_mul, action_inl, action_inr_gen] at hx
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    have := congrArg (fun σ : Perm (X ⊕ X) => σ (Sum.inl x₀)) hx
    simp at this

end C2Wreath
end SymmetricSubgroupAsymptotics
