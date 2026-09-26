import SymmetricSubgroupAsymptotics.GeneratorCosetOrderBound
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

/-!
# Small coset certificates from original binary flip equations

The proposed flip group is the image of a finite binary coefficient space.
Its columns may be dependent and its elements need not belong to the
original generated source. The generic coset theorem only needs this
ambient subgroup to contain the actual transition defects. Consequently
the exact original generator closure has order at most `q * 2^d`, without
an exact kernel chart, representative reachability, or basis independence.

All finite data are ordinary terms and pointwise proof obligations. No
external decision procedure or original-group enumeration is required.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

namespace BinaryFlipCoset

variable {X : Type*} {w d : ℕ}

/-- Explicit spanning expression; dependence among columns is allowed. -/
def bits (columns : Fin d → Fin w → ZMod 2) (c : Fin d → ZMod 2)
    (i : Fin w) : ZMod 2 :=
  ∑ t : Fin d, c t * columns t i

theorem bits_zero (columns : Fin d → Fin w → ZMod 2) :
    bits columns 0 = 0 := by
  funext i
  simp [bits]

theorem bits_add (columns : Fin d → Fin w → ZMod 2)
    (a b : Fin d → ZMod 2) :
    bits columns (a+b) = bits columns a + bits columns b := by
  funext i
  simp only [bits, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- A literal permutation of the original points, defined by its frame. -/
def flip (frame : Fin w × ZMod 2 ≃ X) (v : Fin w → ZMod 2) : Equiv.Perm X where
  toFun x := frame ((frame.symm x).1, (frame.symm x).2 + v (frame.symm x).1)
  invFun x := frame ((frame.symm x).1, (frame.symm x).2 - v (frame.symm x).1)
  left_inv x := by simp
  right_inv x := by simp

theorem flip_apply_frame (frame : Fin w × ZMod 2 ≃ X)
    (v : Fin w → ZMod 2) (p : Fin w × ZMod 2) :
    flip frame v (frame p) = frame (p.1, p.2 + v p.1) := by
  simp only [flip, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

theorem flip_zero (frame : Fin w × ZMod 2 ≃ X) : flip frame 0 = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := frame.surjective x
  rw [flip_apply_frame]
  simp

theorem flip_add (frame : Fin w × ZMod 2 ≃ X) (a b : Fin w → ZMod 2) :
    flip frame (a+b) = flip frame a * flip frame b := by
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := frame.surjective x
  change flip frame (a+b) (frame p) = flip frame a (flip frame b (frame p))
  rw [flip_apply_frame, flip_apply_frame, flip_apply_frame]
  simp only [Pi.add_apply, add_assoc, add_comm (a p.1) (b p.1)]

/-- The image, rather than an independent-column assertion, gives the
ambient subgroup used in the order bound. -/
def coefficientHom (frame : Fin w × ZMod 2 ≃ X)
    (columns : Fin d → Fin w → ZMod 2) :
    Multiplicative (Fin d → ZMod 2) →* Equiv.Perm X where
  toFun c := flip frame (bits columns c.toAdd)
  map_one' := by
    change flip frame (bits columns 0) = 1
    rw [bits_zero, flip_zero]
  map_mul' a b := by
    change flip frame (bits columns (a.toAdd+b.toAdd)) =
      flip frame (bits columns a.toAdd) * flip frame (bits columns b.toAdd)
    rw [bits_add, flip_add]

/-- There are at most `2^d` represented flips, even for dependent columns. -/
theorem coefficient_range_card_le (frame : Fin w × ZMod 2 ≃ X)
    (columns : Fin d → Fin w → ZMod 2) :
    Nat.card (coefficientHom frame columns).range ≤ 2^d := by
  have h := Nat.card_le_card_of_surjective (coefficientHom frame columns).rangeRestrict
    (coefficientHom frame columns).rangeRestrict_surjective
  have hc : Nat.card (Multiplicative (Fin d → ZMod 2)) = 2^d := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  exact h.trans_eq hc

end BinaryFlipCoset

/-- Compact original-point coset data. Every transition is checked as the
actual defect `r_i * g_j * r_next⁻¹`, with an explicit spanning witness. -/
structure BinaryFlipCosetOrderCertificate {X ι : Type*}
    (generators : ι → Equiv.Perm X) (w d q : ℕ) where
  frame : Fin w × ZMod 2 ≃ X
  columns : Fin d → Fin w → ZMod 2
  representatives : Fin q → Equiv.Perm X
  identity : Fin q
  identity_eq : representatives identity = 1
  next : Fin q → ι → Fin q
  coefficients : Fin q → ι → Fin d → ZMod 2
  step : ∀ i j (p : Fin w × ZMod 2),
    (representatives i * generators j * (representatives (next i j))⁻¹) (frame p) =
      frame (p.1, p.2 + BinaryFlipCoset.bits columns (coefficients i j) p.1)

namespace BinaryFlipCosetOrderCertificate

variable {X ι : Type*} {w d q : ℕ} {generators : ι → Equiv.Perm X}
    (C : BinaryFlipCosetOrderCertificate generators w d q)

/-- Only membership of the literal defect in the ambient flip image is
used. Neither the representatives nor all flips must be original words. -/
def toCoset : GeneratorCosetOrderBoundCertificate generators
    (BinaryFlipCoset.coefficientHom C.frame C.columns).range q where
  representatives := C.representatives
  identity := C.identity
  identity_mem := by
    rw [C.identity_eq]
    exact (BinaryFlipCoset.coefficientHom C.frame C.columns).range.one_mem
  next := C.next
  step_mem i j := by
    change ∃ c : Multiplicative (Fin d → ZMod 2),
      BinaryFlipCoset.coefficientHom C.frame C.columns c =
        C.representatives i * generators j * (C.representatives (C.next i j))⁻¹
    refine ⟨Multiplicative.ofAdd (C.coefficients i j), ?_⟩
    apply Equiv.ext
    intro x
    obtain ⟨p, rfl⟩ := C.frame.surjective x
    change BinaryFlipCoset.flip C.frame
      (BinaryFlipCoset.bits C.columns (C.coefficients i j)) (C.frame p) = _
    rw [BinaryFlipCoset.flip_apply_frame]
    exact (C.step i j p).symm

include C in
/-- The upper bound is for the exact original generator closure. -/
theorem card_closure_le [Finite X] :
    Nat.card (Subgroup.closure (Set.range generators)) ≤ q * 2^d :=
  C.toCoset.card_closure_le.trans
    (Nat.mul_le_mul_left q (BinaryFlipCoset.coefficient_range_card_le C.frame C.columns))

include C in
/-- A concrete original-action equality transfers the bound without
changing the points or relying on catalogue order metadata. -/
theorem card_original_le [Finite X] (U : Subgroup (Equiv.Perm X))
    (hsource : U = Subgroup.closure (Set.range generators)) :
    Nat.card U ≤ q * 2^d := by
  rw [hsource]
  exact C.card_closure_le

end BinaryFlipCosetOrderCertificate
end SymmetricSubgroupAsymptotics

end
