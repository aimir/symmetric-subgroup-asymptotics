import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveSimilitudes

/-! An actual linear similitude is represented by an actual original
matrix unit through the checked ambient coordinate equivalence. Its
permutation on the SAME Q-singular points agrees exactly with the
original linear similitude point permutation. This is coordinate
transport, not an abstract recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearSimilitudeCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveGraph
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDSimilitudeGroup
open CFSGOrthogonalDProjectiveSimilitudes
variable (K : Type) [Field K]

def ofLinearEquiv (r : ℕ) (L : (Index r → K) ≃ₗ[K] (Index r → K))
    (c : K) (hc : c ≠ 0)
    (hQ : ∀ v, splitQuadraticForm K r (L v) = c * splitQuadraticForm K r v) :
    similitudes K r :=
  ⟨(ambientLinearEquiv K r).symm L, Units.mk0 c hc, by
    intro v
    have h := hQ v
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply] at h
    change splitQ K (ambientLinearEquiv K r ((ambientLinearEquiv K r).symm L) v) =
      c * splitQ K v
    rw [(ambientLinearEquiv K r).apply_symm_apply]
    exact h⟩

theorem ofLinearEquiv_linear (r : ℕ) (L : (Index r → K) ≃ₗ[K] (Index r → K))
    (c : K) (hc : c ≠ 0)
    (hQ : ∀ v, splitQuadraticForm K r (L v) = c * splitQuadraticForm K r v) :
    ambientLinearEquiv K r (ofLinearEquiv K r L c hc hQ).val = L :=
  (ambientLinearEquiv K r).apply_symm_apply L

theorem ofLinearEquiv_point (r : ℕ) (L : (Index r → K) ≃ₗ[K] (Index r → K))
    (c : K) (hc : c ≠ 0)
    (hQ : ∀ v, splitQuadraticForm K r (L v) = c * splitQuadraticForm K r v) :
    pointHom K r (ofLinearEquiv K r L c hc hQ) =
      CFSGQuadraticSimilitudeGeometry.pointEquiv (splitQuadraticForm K r) L c hc hQ := by
  apply Equiv.ext
  intro P
  apply Subtype.ext
  change P.val.map (ambientLinearEquiv K r (ofLinearEquiv K r L c hc hQ).val).toLinearMap =
    P.val.map L.toLinearMap
  rw [ofLinearEquiv_linear]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearSimilitudeCoordinates
