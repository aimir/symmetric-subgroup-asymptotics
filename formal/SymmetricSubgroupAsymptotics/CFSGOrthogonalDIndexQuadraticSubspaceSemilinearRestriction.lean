import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceProjectiveRestriction
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceSemilinearRestriction

/-! Semilinearity on each original Q-singular subspace of dimension
at least three. Only the general linear-projective transport is reused
from the bilinear packet; the point/plane/subspace carriers here remain
Q-zero, in particular in characteristic two. No extension to the whole
quadratic space or whole-group Out bound is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGPolarSubspacePoints (linearProjectiveEquiv linearProjectiveEquiv_line)
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (f : Points Q ≃ Points Q) (l : Planes Q ≃ Planes Q)
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)

def coordinateRestriction (W : Subspaces Q) (d : ℕ)
    (e : W.val ≃ₗ[K] (Fin d → K))
    (e' : (imageSubspace Q f l hinc W).val ≃ₗ[K] (Fin d → K)) :
    CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Fin d) :=
  ⟨(linearProjectiveEquiv e.symm).trans ((projectiveRestriction Q f l hinc W).trans
    (linearProjectiveEquiv e')), by
    intro p q r
    change (linearProjectiveEquiv e' (projectiveRestriction Q f l hinc W
      (linearProjectiveEquiv e.symm p))).submodule ≤ _ ↔ _
    exact (linearProjectiveEquiv_line e' _ _ _).trans
      ((projectiveRestriction_line Q f l hinc W _ _ _).trans
        (linearProjectiveEquiv_line e.symm p q r))⟩

theorem exists_coordinate_semilinear [Finite K] (W : Subspaces Q) (d : ℕ)
    (e : W.val ≃ₗ[K] (Fin (d + 3) → K))
    (e' : (imageSubspace Q f l hinc W).val ≃ₗ[K] (Fin (d + 3) → K)) :
    ∃ (a : (Fin (d + 3) → K) ≃ₗ[K] (Fin (d + 3) → K)) (s : K ≃+* K),
      ∀ p, (coordinateRestriction Q f l hinc W (d + 3) e e').val p =
        CFSGProjectiveFrameCoordinates.linearPointEquiv a
          (CFSGProjectiveFieldAction.pointEquiv s p) := by
  exact CFSGProjectiveSemilinearDecomposition.exists_decomposition
    (coordinateRestriction Q f l hinc W (d + 3) e e')
    ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
