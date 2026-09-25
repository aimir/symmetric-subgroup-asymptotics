import SymmetricSubgroupAsymptotics.CocycleLifts
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Exact cardinalities of cocycles and coboundaries

The cohomology group here is mathlib's actual first group cohomology,
not a cardinality parameter. In particular the coboundary factor is
retained before it is bounded by the size of the original module.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open groupCohomology

universe u
variable {k B : Type u} [CommRing k] [Group B] (A : Rep k B)

/-- The kernel of the actual map to first cohomology is the actual
coboundary space, including its inclusion into the cocycles. -/
def firstCohomologyKernelEquiv :
    LinearMap.ker (H1π A).hom ≃ coboundaries₁ A where
  toFun z := ⟨z.1.1, (H1π_eq_zero_iff z.1).mp z.2⟩
  invFun z := ⟨coboundariesToCocycles₁ A z,
    (H1π_eq_zero_iff _).mpr z.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

theorem firstCohomologyProjection_surjective : Function.Surjective (H1π A) := by
  intro x
  exact H1_induction_on x (fun z ↦ ⟨z, rfl⟩)

/-- Exact finite or infinite-card convention identity. No finiteness
hypothesis is needed for this quotient-cardinality equality. -/
theorem cocycles_card_eq_coboundaries_mul_H1 :
    Nat.card (cocycles₁ A) = Nat.card (coboundaries₁ A) * Nat.card (H1 A) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (H1π A).hom)]
  rw [Nat.card_congr (firstCohomologyKernelEquiv A)]
  rw [Nat.card_congr ((H1π A).hom.quotKerEquivOfSurjective
    (firstCohomologyProjection_surjective A)).toEquiv]

/-- Coboundaries are the image of the original module under its actual
degree-zero differential. -/
theorem coboundaries_card_le [Finite A] :
    Nat.card (coboundaries₁ A) ≤ Nat.card A := by
  exact Nat.card_le_card_of_surjective
    (fun a : A ↦ (⟨d₀₁ A a, ⟨a, rfl⟩⟩ : coboundaries₁ A))
    (by rintro ⟨z, a, ha⟩; exact ⟨a, Subtype.ext ha⟩)

/-- The exact coboundary factor is the original module modulo its
fixed vectors. The product form is valid without finiteness assumptions. -/
theorem module_card_eq_invariants_mul_coboundaries :
    Nat.card A = Nat.card A.ρ.invariants * Nat.card (coboundaries₁ A) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d₀₁ A).hom)]
  rw [Nat.card_congr (d₀₁ A).hom.quotKerEquivRange.toEquiv]
  rw [d₀₁_ker_eq_invariants]
  rfl

/-- Exact Z1/B1/H1 cardinal identity in the original action. -/
theorem invariants_mul_cocycles_card :
    Nat.card A.ρ.invariants * Nat.card (cocycles₁ A) =
      Nat.card A * Nat.card (H1 A) := by
  rw [cocycles_card_eq_coboundaries_mul_H1, ← mul_assoc,
    ← module_card_eq_invariants_mul_coboundaries]

/-- The full coboundary factor is bounded, never discarded. -/
theorem cocycles_card_le_module_mul_H1 [Finite A] :
    Nat.card (cocycles₁ A) ≤ Nat.card A * Nat.card (H1 A) := by
  rw [cocycles_card_eq_coboundaries_mul_H1]
  exact Nat.mul_le_mul_right _ (coboundaries_card_le A)

end SymmetricSubgroupAsymptotics
