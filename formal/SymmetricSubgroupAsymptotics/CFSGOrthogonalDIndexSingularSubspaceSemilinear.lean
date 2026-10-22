import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularSubspaceAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceSemilinearRestriction

/-! The ACTUAL original projective D automorphism has a semilinear
restriction on every original Q-singular subspace of dimension>=3.
This is a local restriction theorem, not a whole-space extension or
an assumed classical automorphism classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K] [Finite K]

def singularCoordinateRestriction (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5)))
    (W : Subspaces (splitQuadraticForm K (s + 5))) (d : ℕ)
    (e : W.val ≃ₗ[K] (Fin d → K))
    (e' : (singularSubspaceAction K p s f W).val ≃ₗ[K] (Fin d → K)) :
    CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Fin d) :=
  coordinateRestriction (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s f)
    (singularActionHom K p (s + 1) f) (originalPointAction_incidence K p s f) W d e e'

theorem exists_singular_coordinate_semilinear (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5)))
    (W : Subspaces (splitQuadraticForm K (s + 5))) (d : ℕ)
    (e : W.val ≃ₗ[K] (Fin (d + 3) → K))
    (e' : (singularSubspaceAction K p s f W).val ≃ₗ[K] (Fin (d + 3) → K)) :
    ∃ (a : (Fin (d + 3) → K) ≃ₗ[K] (Fin (d + 3) → K)) (σ : K ≃+* K),
      ∀ x, (singularCoordinateRestriction K p s f W (d + 3) e e').val x =
        CFSGProjectiveFrameCoordinates.linearPointEquiv a
          (CFSGProjectiveFieldAction.pointEquiv σ x) :=
  exists_coordinate_semilinear (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s f)
    (singularActionHom K p (s + 1) f) (originalPointAction_incidence K p s f) W d e e'

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
