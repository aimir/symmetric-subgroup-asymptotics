import SymmetricSubgroupAsymptotics.BinaryHeisenberg
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! Affine permutations and affine derivatives on the binary plane. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

@[simp] theorem binaryVector_add_self {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext i
  exact binary_add_self _

instance binaryPlane_kleinFour : IsAddKleinFour (Fin 2 → ZMod 2) where
  card_four := by simp [Nat.card_eq_fintype_card]
  exponent_two := by
    rw [AddMonoid.exponent_eq_of_addEquiv
      (LinearEquiv.piFinTwo (ZMod 2) (fun _ => ZMod 2)).toAddEquiv]
    simp

/-- Every permutation of the four binary-plane points is affine. -/
theorem binaryPlane_permutation_affine (σ : Equiv.Perm (Fin 2 → ZMod 2))
    (x y : Fin 2 → ZMod 2) : σ (x + y) = σ x + σ y + σ 0 := by
  let e : (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2) := σ.trans (Equiv.addRight (σ 0))
  have he : e 0 = 0 := by simp [e]
  let L := IsAddKleinFour.addEquiv e he
  have hadd := L.map_add x y
  change σ (x + y) + σ 0 = (σ x + σ 0) + (σ y + σ 0) at hadd
  rw [show (σ x + σ 0) + (σ y + σ 0) = (σ x + σ y) + (σ 0 + σ 0) by abel,
    binaryVector_add_self, add_zero] at hadd
  calc
    σ (x + y) = (σ (x + y) + σ 0) + σ 0 := by
      rw [add_assoc, binaryVector_add_self, add_zero]
    _ = _ := congrArg (fun v => v + σ 0) hadd

/-- Any affine binary-valued function has its literal dot-product
coordinates; no selected basis or quotient dimension substitutes for it. -/
theorem binary_affine_function_coordinates {m : ℕ} (f : (Fin m → ZMod 2) → ZMod 2)
    (hf : ∀ x y, f (x + y) = f x + f y + f 0) :
    ∃ b : Fin m → ZMod 2, ∀ x, f x = binaryDot b x + f 0 := by
  let L : (Fin m → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => f x + f 0
      map_zero' := binary_add_self _
      map_add' := by
        intro x y
        rw [hf]
        simp [add_assoc, add_comm, add_left_comm] }
  let ℓ := L.toZModLinearMap 2
  let b : Fin m → ZMod 2 := fun i => ℓ (fun j => if i = j then 1 else 0)
  refine ⟨b, ?_⟩
  intro x
  have h := LinearMap.pi_apply_eq_sum_univ ℓ x
  change f x + f 0 = ∑ i, x i * b i at h
  have h' : f x + f 0 = binaryDot b x := by simpa [binaryDot, mul_comm] using h
  calc
    f x = (f x + f 0) + f 0 := by rw [add_assoc, binary_add_self, add_zero]
    _ = _ := congrArg (fun z => z + f 0) h'

/-- Every scalar function on the binary plane has degree at most two.
The coefficients are given by its four original values. -/
theorem binaryPlane_function_polynomial (f : (Fin 2 → ZMod 2) → ZMod 2)
    (x : Fin 2 → ZMod 2) :
    f x = f ![0,0] + (f ![1,0] + f ![0,0]) * x 0 +
      (f ![0,1] + f ![0,0]) * x 1 +
      (f ![1,1] + f ![1,0] + f ![0,1] + f ![0,0]) * x 0 * x 1 := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> simp
  rw [hx]
  have h0 : x 0 = 0 ∨ x 0 = 1 := by
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact h _
  have h1 : x 1 = 0 ∨ x 1 = 1 := by
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact h _
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp [h0, h1, add_assoc, add_comm, add_left_comm]

/-- Every finite difference of a scalar function on the binary plane is
an affine function, including zero displacement. -/
theorem binaryPlane_derivative_affine (f : (Fin 2 → ZMod 2) → ZMod 2)
    (a : Fin 2 → ZMod 2) :
    ∃ b : Fin 2 → ZMod 2, ∃ c : ZMod 2,
      ∀ x, f (x + a) + f x = binaryDot b x + c := by
  let q := f ![1,1] + f ![1,0] + f ![0,1] + f ![0,0]
  let u := f ![1,0] + f ![0,0]
  let v := f ![0,1] + f ![0,0]
  refine ⟨![q * a 1, q * a 0], u * a 0 + v * a 1 + q * a 0 * a 1, ?_⟩
  intro x
  rw [binaryPlane_function_polynomial f (x + a), binaryPlane_function_polynomial f x]
  simp only [binaryDot, Fin.sum_univ_two, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  dsimp [q, u, v]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add, add_zero]

end SymmetricSubgroupAsymptotics
