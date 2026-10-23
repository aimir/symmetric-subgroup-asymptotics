import SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSingularDimension

/-! Coordinate recognition of the literal positive maximal singular
space inside the actual defining-fixed carrier. Vanishing of all negative
coordinates also kills the positive anisotropic coordinate by fixedness;
the proved Witt ceiling gives the exact equality without a form replacement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveSpaceCoordinates
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedA2FixedField CFSGTwistedDMaximalSingularDimension
open CFSGTwistedDFixedVectorParametrization CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

def negativeZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (fixedSpace n q) where
  carrier := {v | ∀ i, v.val (Sum.inr i) = 0}
  zero_mem' := by intro i; rfl
  add_mem' {v w} hx hy := by
    intro i
    change v.val (Sum.inr i) + w.val (Sum.inr i) = 0
    rw [hx i, hy i, add_zero]
  smul_mem' a v hv := by
    intro i
    change (a : q.Extension 2) * v.val (Sum.inr i) = 0
    rw [hv i, mul_zero]

theorem negativeZeroSpace_singular (n : ℕ) (q : CFSG.PrimePower) :
    ∀ v ∈ negativeZeroSpace n q, fixedQuadraticForm n q v = 0 := by
  intro v hv
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
  have hr : rightPart (q.Extension 2) v.val = 0 := by
    funext i
    exact hv i
  change dotProduct (leftPart (q.Extension 2) v.val) (rightPart (q.Extension 2) v.val) = 0
  rw [hr, dotProduct_zero]

theorem positiveSpace_le_negativeZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    positiveSpace n q ≤ negativeZeroSpace n q := by
  rintro v ⟨x, rfl⟩ i
  have hq : q.order ≠ 0 := by
    change q.prime ^ q.exponent ≠ 0
    exact pow_ne_zero _ q.prime_isPrime.ne_zero
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
    simp [positiveEmbedding, fromParameters, hq]

theorem positiveSpace_eq_negativeZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    positiveSpace n q = negativeZeroSpace n q := by
  apply Submodule.eq_of_le_of_finrank_le (positiveSpace_le_negativeZeroSpace n q)
  rw [positiveSpace_finrank]
  exact CFSGTwistedDSingularDimensionBound.singular_finrank_le q n
    (negativeZeroSpace n q) (negativeZeroSpace_singular n q)

theorem mem_positiveSpace_iff (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q) :
    v ∈ positiveSpace n q ↔ ∀ i, v.val (Sum.inr i) = 0 := by
  rw [positiveSpace_eq_negativeZeroSpace]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveSpaceCoordinates
