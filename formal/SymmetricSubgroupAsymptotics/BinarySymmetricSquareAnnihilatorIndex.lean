import SymmetricSubgroupAsymptotics.BinarySymmetricSquareDualOrbit
import SymmetricSubgroupAsymptotics.FieldFunctionalCoordinateCoefficients

/-! An arbitrary base-field subspace missing an off-diagonal vector has
large coupled quotient-index under its actual GL2 congruence stabilizer.
No extension-field linearity of this subspace is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquareAnnihilatorIndex

open BinarySymmetricSquareAction BinaryQuadraticFunctionalStabilizer
open FieldFunctionalCoordinateCoefficients
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private def coordinateFunctional (ℓ : Module.Dual F (Space (K := K))) :
    Module.Dual F (Fin 3 → K) :=
  ℓ.comp (coordinates.toLinearMap.restrictScalars F)

/-- This is the restriction of the actual functional to the off-diagonal line. -/
def centralRestriction (ℓ : Module.Dual F (Space (K := K))) : Module.Dual F K :=
  (coordinateFunctional ℓ).comp (LinearMap.single F (fun _ : Fin 3 => K) 1)

/-- A nonzero off-diagonal restriction gives an actual normalized
quadratic coefficient functional, not merely a scalar-valued analogy. -/
theorem exists_normalized_coefficients [Module.Finite F K]
    (ℓ : Module.Dual F (Space (K := K))) (hf : centralRestriction ℓ ≠ 0) :
    ∃ a c : K, ℓ = functional (centralRestriction ℓ) a 1 c := by
  let f := centralRestriction ℓ
  let l := coordinateFunctional ℓ
  let a := coefficient f hf l (0 : Fin 3)
  let c := coefficient f hf l (2 : Fin 3)
  have h1 : coefficient f hf l (1 : Fin 3) = 1 :=
    coefficient_eq_one_of_single_eq f hf l 1 (fun x => rfl)
  refine ⟨a, c, ?_⟩
  apply LinearMap.ext
  intro S
  have he := apply_eq_sum_coefficients f hf l (coordinates.symm S)
  have hl : l (coordinates.symm S) = ℓ S := by
    change ℓ (coordinates (coordinates.symm S)) = ℓ S
    rw [coordinates.apply_symm_apply]
  calc
    ℓ S = l (coordinates.symm S) := hl.symm
    _ = f (∑ i, coefficient f hf l i * (coordinates.symm S) i) := he
    _ = functional (centralRestriction ℓ) a 1 c S := by
      rw [Fin.sum_univ_three, h1]
      rfl

/-- The annihilator is genuine over F. In the intended application F is
the prime field, so arbitrary additive stabilizers are covered. -/
theorem field_square_le_quotient_card_mul_index
    [Finite F] [Finite K] [CharP K 2]
    (hq : 8 ≤ Nat.card K) (L : Subgroup (GeneralLinear (K := K)))
    (J : Submodule F (Space (K := K)))
    (hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J)
    (t : K) (ht : coordinates (Pi.single (1 : Fin 3) t) ∉ J) :
    Nat.card K ^ 2 ≤ Nat.card (Space (K := K) ⧸ J) * L.index := by
  obtain ⟨φ, hφ⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on
    J (coordinates (Pi.single (1 : Fin 3) t)) ht
  have hf : centralRestriction φ.val ≠ 0 := by
    intro he
    have hz := congrArg (fun f : Module.Dual F K => f t) he
    change φ.val (coordinates (Pi.single (1 : Fin 3) t)) = 0 at hz
    exact hφ hz
  obtain ⟨a, c, heq⟩ := exists_normalized_coefficients φ.val hf
  have hlow : Nat.card K ^ 2 ≤ Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (BinarySymmetricSquareDualOrbit.restrictedCongruence (F := F) (K := K)) φ.val) := by
    rw [heq]
    exact BinarySymmetricSquareDualOrbit.field_square_le_functional_dual_orbit
      hq (centralRestriction φ.val) hf a 1 c one_ne_zero
  have hupper := InvariantAnnihilatorOrbitIndex.dual_orbit_card_le_quotient_card_mul_index
    (BinarySymmetricSquareDualOrbit.restrictedCongruence (F := F) (K := K))
    L J (fun A hA S hS => hJ A hA S hS) φ
  exact hlow.trans hupper

end SymmetricSubgroupAsymptotics.BinarySymmetricSquareAnnihilatorIndex
